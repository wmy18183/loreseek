#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
寻哲 Loreseek (loreseek.cn) local backend.

Why this exists:
  Literature APIs (arXiv in particular) do not send CORS headers, so a browser
  page cannot fetch them directly. This server fetches them server-side and
  serves the page + data from a single origin (local :8899 or any public host).

It also turns "open the article in a new tab" into real in-app reading:
  /api/read  extracts abstract / full text (plain-text last-resort fallback)
  /api/page  fetches + sanitises the ORIGINAL page (markup / CSS / images kept)
             for an iframe srcdoc, so reading is not a TXT dump
  /api/pdf   proxies a PDF through the same origin, so it can be embedded in an
             iframe without X-Frame-Options blocking it.
  /api/enrich  "quick read" metadata: bilingual keywords, Chinese titles and
             takeaways, and a free-access level used to push OA papers first.
  /api/track  topic subscriptions + a background check that pushes only newly
             arrived papers, with free full text first.

Only Python standard library is required.
"""
import quickread
import tracker

import json
import os
import re
import ssl
import glob
import socket
import time
import gzip
import zlib
import base64
import hashlib
import threading
import subprocess
import html as html_lib
import urllib.request
import urllib.parse
import urllib.error
import xml.etree.ElementTree as ET
from html.parser import HTMLParser
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = os.path.dirname(os.path.abspath(__file__))
PORT = int(os.environ.get('PORT') or os.environ.get('LORESEEK_PORT') or '8899')
BIND_HOST = os.environ.get('LORESEEK_BIND', '0.0.0.0')
TIMEOUT = 18
UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) Loreseek/1.0 (xunzhe; local research client)'

_ctx = ssl.create_default_context()
_ctx.check_hostname = False
_ctx.verify_mode = ssl.CERT_NONE

# A VPN client often leaves a system proxy configured even when it is switched
# off. In that state EVERY request fails if we blindly honour the proxy. Keep
# both channels and remember, per host, which one actually worked.
_HAS_PROXY = bool(urllib.request.getproxies())
PROXY_OPENER = urllib.request.build_opener(
    urllib.request.ProxyHandler(urllib.request.getproxies()),
    urllib.request.HTTPSHandler(context=_ctx),
)
DIRECT_OPENER = urllib.request.build_opener(
    urllib.request.ProxyHandler({}),
    urllib.request.HTTPSHandler(context=_ctx),
)
_HOST_KIND = {}
NET = {
    'mode': 'unknown',          # 'global' | 'cn' | 'offline'
    'prefer': 'proxy' if _HAS_PROXY else 'direct',
    'checked': 0,
    'global': None,
    'cn': None,
    'override': None,           # user-forced True / False for cnFirst
    'hint': '',
}
NET_LOCK = threading.Lock()

PROBE_GLOBAL = ('https://api.crossref.org/works?rows=1',
                'https://export.arxiv.org/api/query?id_list=2401.00001')
PROBE_CN = ('https://xueshu.baidu.com', 'https://www.cnki.net')


def _open_with_fallback(req, timeout, deadline=None):
    url = getattr(req, 'full_url', '') or ''
    host = urllib.parse.urlsplit(url).hostname or ''
    first = _HOST_KIND.get(host) or NET['prefer']
    order = [first] + [k for k in ('direct', 'proxy') if k != first]
    last = None
    for kind in order:
        # A stalled channel must not eat the whole budget the second one needs.
        budget = timeout
        if deadline is not None:
            budget = min(timeout, deadline - time.time())
            if budget <= 0.25:
                break
        try:
            r = (DIRECT_OPENER if kind == 'direct' else PROXY_OPENER).open(
                req, timeout=budget)
            _HOST_KIND[host] = kind
            return r
        except Exception as e:
            last = e
    raise last or OSError('network unavailable')


# --------------------------------------------------------------------------
# Wall-clock fencing.
#
# urllib's `timeout` bounds a single socket operation, NOT a request. A proxy
# that accepts the connection and then dribbles bytes resets the timer on
# every recv, so a request nominally capped at 3 s has been observed running
# for 60 s. Anything a reader is actively waiting on therefore runs behind a
# hard wall-clock fence: when the budget is gone we abandon the attempt and
# move on, instead of letting one dead channel define the whole page's speed.
# --------------------------------------------------------------------------
class Deadline(Exception):
    pass


def fence(fn, budget, default=None, swallow=False):
    """Run fn() but give up after `budget` seconds of real time."""
    box = {}
    done = threading.Event()

    def run():
        try:
            box['v'] = fn()
        except BaseException as e:          # noqa: BLE001 - relayed to caller
            box['e'] = e
        finally:
            done.set()

    # Daemon threads: an abandoned attempt must never delay interpreter exit.
    threading.Thread(target=run, daemon=True,
                     name='fence-%s' % getattr(fn, '__name__', 'call')).start()
    if not done.wait(budget):
        if swallow:
            return default
        raise Deadline('gave up after %.1fs' % budget)
    if 'e' in box:
        if swallow:
            return default
        raise box['e']
    return box['v']


FOREIGN_INDEX_HOSTS = ('arxiv.org', 'export.arxiv.org', 'api.crossref.org',
                       'api.openalex.org', 'eutils.ncbi.nlm.nih.gov',
                       'www.ncbi.nlm.nih.gov', 'api.semanticscholar.org',
                       'hn.algolia.com', 'www.nature.com', 'api.core.ac.uk')

# Hosts that really only answer on plain HTTP: everything else gets a TLS
# retry first, because an http request tunnelled through a proxy often stalls.
HTTP_ONLY_HOSTS = ('qikan.cqvip.com', 'www.ncpssd.org')


def get(url, timeout=TIMEOUT, binary=False, max_bytes=32 << 20):
    # With no VPN, unreachable foreign indexes must fail fast: otherwise the
    # streaming search stays "loading" until the slowest one times out.
    host = (urllib.parse.urlsplit(url).hostname or '').lower()
    if (NET['mode'] == 'cn' and timeout > 6 and
            any(host.endswith(h) for h in FOREIGN_INDEX_HOSTS)):
        timeout = 6
    # Two legacy hosts still serve citations over plain HTTP only; everything
    # else is retried over TLS first. Plain-HTTP requests regularly stall
    # inside a proxy tunnel, which showed up as a 12 s wait on arXiv pages.
    tries = [url]
    if url.startswith('http://') and not any(
            host.endswith(h) for h in HTTP_ONLY_HOSTS):
        tries = ['https://' + url[len('http://'):], url]

    # One deadline for the whole exchange: connecting, redirects and the body
    # read all draw from the same budget, so a slow trickle cannot outlive it.
    deadline = time.time() + timeout * 1.5
    last = None
    for i, target in enumerate(tries):
        req = urllib.request.Request(target, headers={
            'User-Agent': UA,
            'Accept': '*/*',
            'Accept-Encoding': 'gzip, deflate',
            'Accept-Language': 'en-US,en;q=0.9,zh-CN;q=0.8',
        })
        try:
            with _open_with_fallback(req, timeout, deadline) as r:
                chunks, size = [], 0
                while True:
                    if time.time() > deadline:
                        raise urllib.error.URLError('transfer deadline exceeded')
                    part = r.read(65536)
                    if not part:
                        break
                    chunks.append(part)
                    size += len(part)
                    if size >= max_bytes:
                        break
                data = b''.join(chunks)
                enc = (r.headers.get('Content-Encoding') or '').lower()
                if enc in ('gzip', 'deflate') and data:
                    try:
                        data = zlib.decompressobj(
                            16 + zlib.MAX_WBITS if enc == 'gzip'
                            else zlib.MAX_WBITS).decompress(data)
                    except zlib.error:
                        pass
                ctype = r.headers.get('Content-Type', '')
            return (data if binary else data.decode('utf-8', 'replace')), ctype
        except Exception as e:
            last = e
            if time.time() > deadline - 0.4:
                break               # no budget left for the second scheme
    raise last or OSError('network unavailable')


class SmartOpener:
    """Adapter so quickread's translation calls share the same network logic."""

    def open(self, req, timeout=TIMEOUT):
        return _open_with_fallback(req, timeout)


OPENER = SmartOpener()


# Publishers often ship inline markup inside titles ("...targeting <i>S</i>-
# <i>S</i>..."). Left as-is it shows up as literal tag text in the product.
# One display-layer normaliser covers every JSON and SSE endpoint at once.
# Only genuine markup-shaped tags are removed (name + optional key="value"
# attributes). A math-looking fragment such as "A<B and C>D" is left alone.
_INLINE_TAG_RE = re.compile(
    r'</?([a-z][a-z0-9]*)(?:\s+[a-z-]+\s*=\s*"[^"]*")*\s*/?>', re.I)
_INLINE_ALLOWED = {'i', 'b', 'em', 'strong', 'sub', 'sup', 'u', 'small',
                   'big', 'span', 'font', 'mark', 'br', 'p', 'div', 'li',
                   'ul', 'ol', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'a'}
_INLINE_SPACE = {'br', 'p', 'div', 'li', 'ul', 'ol',
                 'h1', 'h2', 'h3', 'h4', 'h5', 'h6'}
_DISPLAY_TEXT_KEYS = {'title', 'titleZh', 'abstract', 'summary', 'journal',
                      'authors', 'note', 'snippet', 'subtitle', 'caption'}


def _strip_inline(m):
    name = m.group(1).lower()
    if name not in _INLINE_ALLOWED:
        return m.group(0)
    return ' ' if name in _INLINE_SPACE else ''


def _plain_text(v):
    # Feeds that double-escape markup ship titles like
    # "&lt;span&gt;BAM 5.0&lt;/span&gt;". Unescape first so the tag stripper
    # sees a real tag, then collapse the whitespace it leaves behind.
    v = html_lib.unescape(v)
    return re.sub(r'\s{2,}', ' ', _INLINE_TAG_RE.sub(_strip_inline, v)).strip()


def _clean_display(obj):
    if isinstance(obj, dict):
        out = {}
        for k, v in obj.items():
            if k in _DISPLAY_TEXT_KEYS:
                if isinstance(v, str):
                    v = _plain_text(v)
                elif isinstance(v, list):
                    v = [_plain_text(x) if isinstance(x, str) else x for x in v]
            out[k] = _clean_display(v) if isinstance(v, (dict, list)) else v
        return out
    if isinstance(obj, list):
        return [_clean_display(x) for x in obj]
    return obj


def _tcp_get(opener, url, timeout):
    req = urllib.request.Request(url, headers={'User-Agent': UA,
                                               'Accept': '*/*'})
    with opener.open(req, timeout=timeout) as r:
        r.read(256)
    return True


def probe_network(force=False):
    """Decide whether global literature indexes are reachable.

    Runs off the request path (and cached for 5 min) so it never slows a
    search down. Result drives the front-end 'domestic sources first' mode.
    """
    if (not force and NET['checked'] and
            time.time() - NET['checked'] < 300):
        return net_status()
    results = {}

    def one(label, kind, url):
        op = DIRECT_OPENER if kind == 'direct' else PROXY_OPENER
        try:
            results[label] = _tcp_get(op, url, 3.5)
        except Exception:
            results[label] = False

    with ThreadPoolExecutor(max_workers=4) as pool:
        jobs = [pool.submit(one, 'g_direct', 'direct', PROBE_GLOBAL[0]),
                pool.submit(one, 'g_proxy', 'proxy', PROBE_GLOBAL[1]),
                pool.submit(one, 'c_direct', 'direct', PROBE_CN[0]),
                pool.submit(one, 'c_proxy', 'proxy', PROBE_CN[1])]
        for f in jobs:
            try:
                f.result()
            except Exception:
                pass

    global_ok = bool(results.get('g_direct') or results.get('g_proxy'))
    cn_ok = bool(results.get('c_direct') or results.get('c_proxy'))
    with NET_LOCK:
        NET['global'] = global_ok
        NET['cn'] = cn_ok
        NET['mode'] = 'global' if global_ok else ('cn' if cn_ok else 'offline')
        NET['checked'] = time.time()
        if not global_ok and results.get('g_proxy') and not results.get('g_direct'):
            NET['prefer'] = 'proxy'
        elif not global_ok and results.get('g_direct'):
            NET['prefer'] = 'direct'
        NET['hint'] = ('全球成果已连接' if NET['mode'] == 'global' else
                       '智能择优检索' if cn_ok else
                       '正在为你准备内容')
        _HOST_KIND.clear()
    return net_status()


def net_status():
    with NET_LOCK:
        forced = NET['override']
        mode = NET['mode']
        cn_first = (mode == 'cn') if forced is None else bool(forced)
        return {
            'ok': True,
            'mode': mode,
            'cnFirst': cn_first,
            'forced': forced,
            'global': NET['global'],
            'cn': NET['cn'],
            'proxyConfigured': _HAS_PROXY,
            'prefer': NET['prefer'],
            'hint': NET['hint'],
            'checked': NET['checked'],
        }


# ---------------------------------------------------------------- text extract
SKIP_TAGS = {'script', 'style', 'nav', 'header', 'footer', 'aside', 'form',
             'noscript', 'svg', 'iframe', 'button', 'select', 'option'}
BLOCK_TAGS = {'p', 'br', 'div', 'h1', 'h2', 'h3', 'h4', 'h5', 'li', 'tr',
              'section', 'article', 'blockquote', 'pre', 'td'}


class TextExtractor(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in SKIP_TAGS:
            self.skip += 1
        elif tag in BLOCK_TAGS:
            self.parts.append('\n')

    def handle_endtag(self, tag):
        if tag in SKIP_TAGS and self.skip > 0:
            self.skip -= 1
        if tag in BLOCK_TAGS:
            self.parts.append('\n')

    def handle_data(self, data):
        if self.skip == 0:
            self.parts.append(data)

    def text(self):
        t = html_lib.unescape(''.join(self.parts))
        t = re.sub(r'[ \t\r\f\v]+', ' ', t)
        t = re.sub(r' *\n *', '\n', t)
        t = re.sub(r'\n{3,}', '\n\n', t)
        return t.strip()


def html_to_text(raw, limit=30000):
    ex = TextExtractor()
    try:
        ex.feed(raw)
        return ex.text()[:limit]
    except Exception:
        return re.sub(r'<[^>]+>', ' ', raw)[:limit]


# ------------------------------------------------------------ original page
# "直接阅读" must look like the publisher's page, not a plain TXT dump.
# Fetch the real HTML, keep its markup / CSS / images, and only neutralise what
# would break a sandboxed in-app iframe (scripts, meta refresh, CSP, forms,
# javascript: URLs). A <base href> keeps all relative images / CSS working.
PAGE_CACHE = {}
PAGE_RAW_CACHE = {}          # original bytes, reused by the full-text view
PDF_CACHE = {}
ASSET_CACHE = {}
CACHE_TTL = 600
CACHE_MAX = 12

# A broken asset must never show the browser's "torn image" icon. Serve a soft
# neutral placeholder instead; the surrounding layout stays intact.
PLACEHOLDER_SVG = (
    b'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 320 180" '
    b'width="320" height="180"><rect width="320" height="180" fill="#eef1f6"/>'
    b'<g fill="none" stroke="#c3cbd9" stroke-width="4" stroke-linejoin="round">'
    b'<rect x="112" y="56" width="96" height="70" rx="8"/>'
    b'<circle cx="137" cy="82" r="8"/>'
    b'<path d="M118 118l26-24 20 18 14-12 24 22"/></g>'
    b'<text x="160" y="152" text-anchor="middle" font-family="sans-serif" '
    b'font-size="12" fill="#9aa5b6">\xe5\x9b\xbe\xe7\x89\x87\xe6\x9a\x82\xe4\xb8\x8d\xe5\x8f\xaf\xe7\x94\xa8</text></svg>')
BLANK_PNG = base64.b64decode(
    'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVQImWP4z8DwHwAF'
    'AAH/q842iQAAAABJRU5ErkJggg==')

BOOL_ATTRS = {'allowfullscreen', 'async', 'autoplay', 'checked', 'controls',
              'default', 'defer', 'disabled', 'hidden', 'ismap', 'loop',
              'multiple', 'muted', 'nomodule', 'novalidate', 'open',
              'playsinline', 'readonly', 'required', 'reversed', 'selected',
              'itemscope'}
VOID_TAGS = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input',
             'link', 'meta', 'param', 'source', 'track', 'wbr'}
DROP_CONTENT = {'script', 'noscript', 'iframe', 'object', 'embed', 'applet',
                'template'}
DROP_TAG_ONLY = {'base', 'form'}
LAZY_ATTRS = ('data-src', 'data-original', 'data-lazy-src',
              'data-original-src', 'data-url', 'data-echo')


# ------------------------------------------------------------ brand theming
# 寻哲 (loreseek.cn) reader theme. Pages from ANY publisher should feel like
# the same product: same blue accent, neutral surfaces and typography.
# Every node stays — text, images, links, layout are NOT removed; we only
# restyle colours / radii / shadows. Ad slots and "open the app" jump-bait are
# hidden with CSS (and ad links neutralised), never deleted from the DOM.
_LS_LIGHT = ("--ls-bg:#f5f7fa;--ls-card:#ffffff;--ls-hover:#eef1f6;"
             "--ls-text:#1a1a2e;--ls-sub:#6b7280;--ls-muted:#9ca3af;"
             "--ls-border:#e5e7eb;--ls-accent:#2563eb;--ls-soft:#dbeafe;"
             "--ls-accent-hover:#1d4ed8;--ls-radius:10px;"
             "--ls-shadow:0 1px 3px rgba(0,0,0,.08)")
_LS_DARK = ("--ls-bg:#0f1117;--ls-card:#1a1d27;--ls-hover:#252836;"
            "--ls-text:#e4e6eb;--ls-sub:#9ca3af;--ls-muted:#6b7280;"
            "--ls-border:#2a2d3a;--ls-accent:#3b82f6;--ls-soft:#1e293b;"
            "--ls-accent-hover:#60a5fa;--ls-radius:10px;"
            "--ls-shadow:0 1px 3px rgba(0,0,0,.3)")
# The parent app pushes data-theme="light|dark" into the srcdoc <html> root;
# the media query is only a fallback for previews opened without the app.
_LS_VARS = (':root{' + _LS_LIGHT + '}'
            '[data-theme="dark"]{' + _LS_DARK + '}'
            '@media(prefers-color-scheme:dark){'
            ':root:not([data-theme]){' + _LS_DARK + '}}')

_LS_RULES = """
html,body{background-color:var(--ls-bg)!important;background-image:none!important;
 color:var(--ls-text)!important;line-height:1.8;
 font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"PingFang SC","Microsoft YaHei",sans-serif!important}
h1,h2,h3,h4,h5,h6{color:var(--ls-text)!important}
p,li,dd,dt,td,th,figcaption,blockquote{color:var(--ls-text)!important}
a,a:visited{color:var(--ls-accent)!important}
a:hover{color:var(--ls-accent-hover)!important}
:is(article,main,[role="main"],.article,.article-content,.content,.post,.post-content,
 .entry,.entry-content,#content,.main-content,.detail-content,.paper-content,
 .card,.panel,.box,.reader,.markdown-body,
 .hero,.jumbotron,.masthead,.topbar,.page-header,.cover,.title-bar){
 background-color:var(--ls-card)!important;background-image:none!important;
 color:var(--ls-text)!important;border-color:var(--ls-border)!important;
 border-radius:var(--ls-radius)!important;box-shadow:var(--ls-shadow)!important}
:is(header,nav,footer,aside,.header,.nav,.footer,.sidebar){
 background-color:var(--ls-card)!important;background-image:none!important;
 border-color:var(--ls-border)!important}
:is(table,thead,tbody,tr,td,th,hr,pre,figure,img,video){
 border-color:var(--ls-border)!important}
:is(blockquote,pre,.quote,.highlight){background-color:var(--ls-soft)!important;
 border-left:3px solid var(--ls-accent)!important;border-radius:8px!important}
code{background-color:var(--ls-hover)!important;border-radius:4px!important}
:is(button,[role="button"],.btn,.button,input[type="button"],input[type="submit"]){
 background-color:var(--ls-accent)!important;color:#fff!important;
 border:1px solid transparent!important;border-radius:8px!important}
a:is(.btn,.button,[role="button"]){text-decoration:none!important;color:#fff!important}
:is(input:not([type="button"]):not([type="submit"]),textarea,select){
 background-color:var(--ls-card)!important;color:var(--ls-text)!important;
 border:1px solid var(--ls-border)!important;border-radius:8px!important}
:is(ins.adsbygoogle,iframe[src*="doubleclick" i],iframe[src*="googlesyndication" i],
 [data-ad-slot],[data-ad-client],[data-ad-status],a[data-loreseek-muted="ad"],
 [class*="advertis" i],[id*="advertis" i],[class*="adsbygoogle" i],[id*="adsbygoogle" i],
 [class*="ad-slot" i],[id*="ad-slot" i],[class*="ad-container" i],
 [class*="ad-banner" i],[class*="banner-ad" i],[class*="float-ad" i],
 [class*="popup-ad" i],[class*="sponsored" i],[class*="sponsor-ad" i],
 [class*="qrcode" i],[class*="qr-code" i],[class*="app-download" i],
 [class*="download-app" i],[class*="open-app" i],[class*="openapp" i],
 [class*="share-bar" i],[class*="sharebar" i],
 [aria-label*="广告"],[title*="广告"]){display:none!important}
"""
BRAND_THEME_CSS = _LS_VARS + _LS_RULES

# Only unambiguous ad / app-jump destinations are neutralised. Normal article
# links (including "查看原站") are untouched.
AD_JUMP_RE = re.compile(
    r'(?i)(doubleclick|googlesyndication|adservice|adsystem|/ads?/|'
    r'advertis|sponsored|qrcode|qr[-_]?code|app[-_]?download|download[-_]?app|'
    r'open[-_]?app|weixin://|mqq://|alipays://|data-ad-|'
    r'(?:^|[^a-z])ad(?:slot|box|banner|container|wrapper)(?:[^a-z]|$))')

# Never let the ad filter touch scholarly content: PDFs, figures, tables,
# supplements, references and full-text links always stay live and visible.
ACADEMIC_LINK_RE = re.compile(
    r'(?i)(doi\.org|\.pdf|/pdf|full[-_ ]?text|download[-_ ]?pdf|supplement|'
    r'supplementary|figure|table|appendix|reference|citation|'
    r'全文|下载论文|参考文献|图表|附件|原文|正文)')


class PageSanitizer(HTMLParser):
    """Rebuild a page verbatim, minus anything that could navigate or execute."""

    def __init__(self, base_url):
        super().__init__(convert_charrefs=False)
        self.base_url = base_url
        self.out = []
        self.skip = 0
        self.head_started = False
        self.injected_start = False
        self.injected_end = False
        self.declared = False

    def _head_start(self):
        return ('<meta charset="utf-8"><meta name="referrer" content="no-referrer">'
                '<base href="%s" target="_blank">' %
                html_lib.escape(self.base_url, quote=True))

    def _head_end(self):
        # Layout stays exactly as the publisher built it. These rules only fix
        # the "half loaded" look (broken images, empty JS carousels); then the
        # 寻哲 brand layer harmonises colours with the host app and hides ads.
        return ('<style data-loreseek="1">'
                'html,body{overflow-x:hidden!important}'
                'img,video,canvas{max-width:100%!important}'
                'img{object-fit:contain;background:#f4f5f8}'
                'img:not([src]),img[src=""],img[src="#"]{display:none!important}'
                '.tr-img-ph{display:none!important}'
                'iframe,object,embed,applet{display:none!important}'
                '[class*="carousel"]:empty,[class*="slider"]:empty,'
                '[id*="carousel"]:empty,[id*="slider"]:empty{display:none!important}'
                'pre,code{white-space:pre-wrap!important;word-break:break-word!important}'
                + BRAND_THEME_CSS + '</style>')

    def _abs(self, v):
        return urllib.parse.urljoin(self.base_url, (v or '').strip())

    def _asset(self, v):
        """Route original images through our own proxy: the browser never
        needs a direct connection to the publisher (and no hotlink blocking)."""
        v = (v or '').strip()
        if not v or v.startswith(('data:', 'blob:', 'about:', '#')):
            return v
        a = self._abs(v)
        if not a.startswith(('http://', 'https://')):
            return v
        return '/api/asset?url=%s' % urllib.parse.quote(a, safe='')

    def _srcset(self, v):
        v = (v or '').strip()
        if v.startswith('data:'):
            return v
        out = []
        for seg in v.split(','):
            bits = seg.strip().split()
            if not bits:
                continue
            bits[0] = self._asset(bits[0])
            out.append(' '.join(bits))
        return ', '.join(out)

    def _clean_attrs(self, tag, attrs):
        d = {}
        for k, v in attrs:
            if k:
                d[k.lower()] = '' if v is None else v
        for k in list(d):
            if k.startswith('on') or k in ('srcdoc', 'integrity', 'crossorigin',
                                           'formaction', 'ping'):
                d.pop(k, None)
        for k in ('href', 'src', 'poster', 'action', 'xlink:href', 'data'):
            v = (d.get(k) or '').strip()
            if v.lower().replace('\x00', '').startswith(
                    ('javascript:', 'vbscript:', 'data:text/html')):
                d[k] = '#'
        if re.search(r'javascript:|expression\(|behaviour\s*:',
                     d.get('style', ''), re.I):
            d.pop('style', None)
        if tag in ('img', 'source', 'video', 'audio'):
            src = (d.get('src') or '').strip()
            if (not src or src.lower().startswith('data:image/gif') or
                    'placeholder' in src.lower()):
                for la in LAZY_ATTRS:
                    if (d.get(la) or '').strip():
                        d['src'] = d[la]
                        break
            if not (d.get('src') or '').strip() and (d.get('data-srcset') or '').strip():
                d['srcset'] = d['data-srcset']
            d.pop('loading', None)       # no JS left to trigger lazy loading
            # Rewrite subresources to our own proxy so original styling /
            # images load even when the publisher blocks direct hotlinking.
            if d.get('src'):
                d['src'] = self._asset(d['src'])
            if d.get('srcset'):
                d['srcset'] = self._srcset(d['srcset'])
            if d.get('poster'):
                d['poster'] = self._asset(d['poster'])
        if tag == 'a':
            d['target'] = '_blank'
            d['rel'] = 'noopener noreferrer'
            # Ad / app-jump links: keep the node and its text, just disable the
            # jump and mark it for the brand CSS. Every other link stays live.
            blob = ' '.join('%s=%s' % (k, v) for k, v in d.items()).lower()
            if AD_JUMP_RE.search(blob) and not ACADEMIC_LINK_RE.search(blob):
                d['href'] = '#'
                d['target'] = '_self'
                d['data-loreseek-muted'] = 'ad'
        return d

    def _render_tag(self, tag, attrs, selfclose=False):
        d = self._clean_attrs(tag, attrs)
        s = '<' + tag
        for k, v in d.items():
            if v == '' and k in BOOL_ATTRS:
                s += ' ' + k
            else:
                s += ' %s="%s"' % (k, html_lib.escape(str(v), quote=True))
        return s + (' />' if selfclose else '>')

    def handle_decl(self, decl):
        self.declared = True
        self.out.append('<!DOCTYPE html>')

    def _img_ok(self, attrs):
        """Drop image tags that have no real source (a JS-lazy placeholder
        would otherwise render as a broken-image icon in the reader)."""
        src = (self._clean_attrs('img', attrs).get('src') or '').strip()
        return bool(src) and not src.lower().startswith(('data:image/gif',
                                                          'data:image/png;base64,ivbor'))

    def handle_starttag(self, tag, attrs):
        if self.skip:
            if tag not in VOID_TAGS:
                self.skip += 1
            return
        if tag in DROP_CONTENT:
            self.skip = 1
            return
        if tag in DROP_TAG_ONLY:
            return
        if tag == 'img' and not self._img_ok(attrs):
            self.out.append('<span class="tr-img-ph"></span>')
            return
        if tag == 'meta':
            d = {k.lower(): (v or '') for k, v in attrs if k}
            # We re-encode everything as UTF-8: keeping the original charset
            # declaration would make the browser decode our output twice.
            if d.get('charset') or d.get('http-equiv', '').lower() == 'content-type':
                return
            if d.get('http-equiv', '').lower() in (
                    'refresh', 'content-security-policy', 'x-frame-options', 'set-cookie'):
                return
            if d.get('name', '').lower() == 'referrer':
                return
        if tag == 'head':
            self.head_started = True
            self.out.append(self._render_tag(tag, attrs))
            self.out.append(self._head_start())
            self.injected_start = True
            return
        if tag == 'body' and not self.injected_start:
            self.out.append(self._head_start())
            self.injected_start = True
        self.out.append(self._render_tag(tag, attrs))

    def handle_startendtag(self, tag, attrs):
        if self.skip or tag in DROP_CONTENT or tag in DROP_TAG_ONLY:
            return
        if tag == 'img':
            self.out.append('<span class="tr-img-ph"></span>' if not self._img_ok(attrs)
                            else self._render_tag(tag, attrs, True))
            return
        if tag == 'meta':
            d = {k.lower(): (v or '') for k, v in attrs if k}
            if (d.get('charset') or d.get('http-equiv') or
                    d.get('name', '').lower() == 'referrer'):
                return
        self.out.append(self._render_tag(tag, attrs, True))

    def handle_endtag(self, tag):
        if self.skip:
            self.skip -= 1
            return
        if tag in DROP_CONTENT or tag in DROP_TAG_ONLY or tag in VOID_TAGS:
            return
        if tag == 'head':
            self.out.append(self._head_end())
            self.injected_end = True
        self.out.append('</%s>' % tag)

    def handle_data(self, data):
        if not self.skip:
            self.out.append(data)

    def handle_entityref(self, name):
        if not self.skip:
            self.out.append('&%s;' % name)

    def handle_charref(self, name):
        if not self.skip:
            self.out.append('&#%s;' % name)

    def handle_comment(self, data):
        if not self.skip:
            self.out.append('<!--%s-->' % data.replace('-->', ''))

    def handle_pi(self, data):
        pass

    def result(self):
        body = ''.join(self.out)
        extras = self._head_start() + self._head_end()
        if not self.head_started:
            body = ('<!DOCTYPE html><html><head>' + extras + '</head><body>' +
                    body + '</body></html>')
        else:
            if not self.injected_end:
                body = (body.replace('<body', extras + '<body', 1)
                        if '<body' in body else extras + body)
            if not self.declared:
                body = '<!DOCTYPE html>' + body
        return body[:2000000]


def asset_url(u):
    return '/api/asset?url=%s' % urllib.parse.quote(u, safe='')


def _link_css(html, url):
    """Route stylesheets through the local asset proxy, but do NOT fetch them
    server-side. The browser loads them in parallel (first paint in ~1s) and
    /api/asset rebases their url()/@import references. No more 18s waits for
    a slow publisher stylesheet.
    """
    def repl(m):
        tag = m.group(0)
        low = tag.lower()
        if 'stylesheet' not in low:
            return '' if 'as="script"' in low else tag
        hm = re.search(r'href="([^"]+)"', tag, re.I)
        if not hm:
            return ''
        a = urllib.parse.urljoin(url, html_lib.unescape(hm.group(1)))
        if not a.startswith(('http://', 'https://')):
            return ''
        return '<link rel="stylesheet" href="%s">' % asset_url(a)

    return re.sub(r'<link\b[^>]*>', repl, html, flags=re.I)


def rebase_css(css, css_url):
    """Rewrite url() / @import inside a proxied stylesheet to absolute proxy
    URLs, otherwise the browser resolves them against /api/asset?... and they
    all break (fonts, background images, sprites)."""
    def fix(m):
        v = m.group(2).strip()
        if v.startswith(('data:', '#')):
            return m.group(0)
        return 'url("%s")' % asset_url(urllib.parse.urljoin(css_url, v))

    css = re.sub(r'url\(\s*([\'"]?)([^)\'\"]+)\1\s*\)', fix, css)
    css = re.sub(r'@import\s+url\(\s*([\'"]?)([^)\'\"]+)\1\s*\)',
                 lambda m: '@import url("%s")' % asset_url(
                     urllib.parse.urljoin(css_url, m.group(2))), css, flags=re.I)
    css = re.sub(r'@import\s+(["\'])([^"\']+)\1',
                 lambda m: '@import "%s"' % asset_url(
                     urllib.parse.urljoin(css_url, m.group(2))), css, flags=re.I)
    return css


def _proxy_style_blocks(html, base):
    """Relative url() inside the page's own <style> blocks also goes through
    the local asset proxy (fonts / background images stay intact)."""
    def fix(m):
        v = m.group(2).strip()
        if v.startswith(('data:', 'http://', 'https://', '//', '#')):
            return m.group(0)
        a = urllib.parse.urljoin(base, v)
        return 'url("/api/asset?url=%s")' % urllib.parse.quote(a, safe='')

    def on_style(m):
        return (m.group(1) +
                re.sub(r'url\(\s*([\'"]?)([^)\'\"]+)\1\s*\)', fix, m.group(2)) +
                m.group(3))
    return re.sub(r'(<style\b[^>]*>)(.*?)(</style>)', on_style, html,
                  flags=re.S | re.I)


def _decode_page(raw, ct):
    """Honour the page's own charset (many CN journal sites are still GBK)."""
    low = (ct or '').lower()
    enc = 'utf-8'
    m = re.search(r'charset\s*=\s*[\'"]?([\w\-]+)', low)
    if m:
        enc = m.group(1)
    if enc.lower() in ('utf-8', 'utf8'):
        m2 = re.search(br'charset\s*=\s*[\'"]?([\w\-]+)', raw[:4096], re.I)
        if m2:
            e2 = m2.group(1).decode('ascii', 'ignore')
            if e2.lower() not in ('utf-8', 'utf8'):
                enc = e2
    try:
        return raw.decode(enc, 'replace').lstrip('\ufeff')
    except LookupError:
        return raw.decode('utf-8', 'replace').lstrip('\ufeff')


def _page_to_html(raw, ct, url):
    """Decode + sanitise a fetched page into a layout-preserving srcdoc."""
    low = (ct or '').lower()
    head = raw[:512].lstrip().lower()
    if raw[:4] == b'%PDF' or ('html' not in low and not (
            head.startswith(b'<!doctype') or head.startswith(b'<html'))):
        return None
    text = _decode_page(raw, ct)
    s = PageSanitizer(url)
    try:
        s.feed(text)
        s.close()
        return _proxy_style_blocks(_link_css(s.result(), url), url)
    except Exception:
        return ('<!DOCTYPE html><html><head><meta charset="utf-8"></head><body>'
                '<p>内容正在准备中，请稍候。</p></body></html>')


PAGE_FAIL_CACHE = {}


def fetch_page(url):
    """Return a sanitised, layout-preserving copy of the publisher's page.

    Direct fetch plus read-only raw proxies race each other, so a slow mirror
    never makes the reader wait: the first usable ORIGINAL HTML wins (usually
    the direct one in 1-4s). A TXT dump is only ever the last-resort fallback.
    """
    hit = PAGE_CACHE.get(url)
    if hit and time.time() - hit[0] < CACHE_TTL:
        return hit[1]
    # A page that just failed for all three channels must not cost another
    # full race: the reader falls back to the text view while this cools down.
    fail = PAGE_FAIL_CACHE.get(url)
    if fail and time.time() - fail < 30:
        return {'ok': False, 'html': '', 'error': '网页全文暂不可用'}
    q = urllib.parse.quote(url, safe='')
    targets = [
        ('direct', url),
        ('raw proxy', 'https://api.allorigins.win/raw?url=' + q),
        ('raw proxy 2', 'https://api.codetabs.com/v1/proxy?quest=' + q),
    ]

    def worker(label, target):
        raw, ct = get(target, timeout=5, binary=True)
        page = _page_to_html(raw, ct, url)
        good = bool(page and len(page) > 300)
        if good:
            PAGE_RAW_CACHE[url] = (time.time(), raw, ct)
            if len(PAGE_RAW_CACHE) >= CACHE_MAX * 2:
                for k in sorted(PAGE_RAW_CACHE,
                                key=lambda k: PAGE_RAW_CACHE[k][0])[:4]:
                    PAGE_RAW_CACHE.pop(k, None)
        return label, (page if good else '')

    html, via, last_err = '', '', ''
    pool = ThreadPoolExecutor(max_workers=3)
    futures = [pool.submit(worker, label, target) for label, target in targets]
    try:
        for f in as_completed(futures, timeout=5.5):
            try:
                label, page = f.result()
            except Exception as e:
                last_err = '%s: %s' % (type(e).__name__, str(e)[:60])
                continue
            if page:
                html, via = page, label
                break
    except Exception:
        last_err = last_err or '抓取超时'
    finally:
        pool.shutdown(wait=False)
        for f in futures:
            f.cancel()

    if html:
        payload = {'ok': True, 'html': html, 'url': url, 'via': via,
                   'note': '网页全文 · 完整保留正文、图表与参考文献，统一寻哲主题风格'}
        PAGE_FAIL_CACHE.pop(url, None)
    else:
        payload = {'ok': False, 'html': '', 'error': '网页全文暂不可用'}
        PAGE_FAIL_CACHE[url] = time.time()
        if len(PAGE_FAIL_CACHE) > 400:
            PAGE_FAIL_CACHE.clear()
    # Never cache a transient failure for 10 minutes: a single timeout used to
    # make the original view permanently unavailable until restart.
    if html:
        if len(PAGE_CACHE) >= CACHE_MAX:
            for k in sorted(PAGE_CACHE, key=lambda k: PAGE_CACHE[k][0])[:4]:
                PAGE_CACHE.pop(k, None)
        PAGE_CACHE[url] = (time.time(), payload)
    return payload


def cached_asset(target):
    hit = ASSET_CACHE.get(target)
    if hit and time.time() - hit[0] < CACHE_TTL:
        return hit[1], hit[2]
    raw, ct = get(target, timeout=14, binary=True)
    ctype = (ct or '').split(';')[0].strip() or 'application/octet-stream'
    if ctype == 'text/css' or target.lower().split('?')[0].endswith('.css'):
        ctype = 'text/css; charset=utf-8'
        try:
            raw = rebase_css(raw.decode('utf-8', 'replace'), target).encode('utf-8')
        except Exception:
            pass
    if len(ASSET_CACHE) >= CACHE_MAX * 4:
        for k in sorted(ASSET_CACHE, key=lambda k: ASSET_CACHE[k][0])[:12]:
            ASSET_CACHE.pop(k, None)
    ASSET_CACHE[target] = (time.time(), raw, ctype)
    return raw, ctype


class PdfBlocked(Exception):
    """PDF could not be obtained, with a reason a reader can act on."""

    def __init__(self, reason, hint=''):
        super().__init__(reason)
        self.reason = reason
        self.hint = hint


# PMC (US NIH) protects its PDFs with a proof-of-work handshake: the first
# request returns an HTML page holding a challenge; the browser must find a
# nonce whose SHA-256(challenge+nonce) starts with `difficulty` zeros, store
# it in a cookie and re-request. We replicate that handshake server-side so
# open-access PDFs keep working without a real browser.


def _solve_pmc_pow(html):
    ch = re.search(r'POW_CHALLENGE\s*=\s*"([^"]+)"', html)
    if not ch:
        return None
    challenge = ch.group(1)
    df = re.search(r'POW_DIFFICULTY\s*=\s*"(\d+)"', html)
    difficulty = int(df.group(1)) if df else 4
    prefix = '0' * difficulty
    ck = re.search(r'POW_COOKIE_NAME\s*=\s*"([^"]+)"', html)
    cookie_name = ck.group(1) if ck else 'cloudpmc-viewer-pow'
    nonce = 0
    # SHA-256 in the page's vendor bundle; difficulty 4 needs ~65k hashes (<1s).
    while nonce < 50_000_000:
        if hashlib.sha256((challenge + str(nonce)).encode()).hexdigest().startswith(prefix):
            return '%s=%s,%d' % (cookie_name, challenge, nonce)
        nonce += 1
    return None


# ---------------------------------------------------------------------------
# PDF acquisition. Publisher CDNs increasingly challenge non-browser clients
# (403 / JS check). We lower that risk instead of surfacing it to the reader:
#   1. browser-shaped headers, plus a warm-up visit to the article landing page
#      so a retried PDF request carries a real session cookie and Referer;
#   2. repository URL variants (arXiv / PMC / DOI resolver);
#   3. a DOI-based open-access resolver (Unpaywall / OpenAlex / Semantic Scholar
#      / Crossref) that locates a legally free copy when the publisher blocks.
# Every lookup is bounded in time and cached; a miss silently hands the reader
# over to the full-text web view. No anti-bot wording ever reaches the UI.
# ---------------------------------------------------------------------------
BROWSER_UA = ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
              '(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36')
OA_EMAIL = os.environ.get('LORESEEK_OA_EMAIL', 'contact@loreseek.cn')
OA_CACHE = {}
OA_LOCK = threading.Lock()


def _json_api(url, timeout=5):
    raw, _ = get(url, timeout=timeout, binary=True)
    return json.loads(raw.decode('utf-8', 'replace'))


def _collect_oa_urls(doi, title, target):
    """Legally open PDF locations for a DOI, most promising first."""
    key = (doi or '') + '|' + (title or '')[:100] + '|' + target
    with OA_LOCK:
        hit = OA_CACHE.get(key)
        if hit and time.time() - hit[0] < 1800:
            return hit[1]
    d = re.sub(r'^https?://(?:dx\.)?doi\.org/', '', (doi or '').strip(),
               flags=re.I).strip()
    urls = []

    def add(u):
        if isinstance(u, str) and u.startswith(('http://', 'https://')) and u not in urls:
            urls.append(u)

    jobs = []
    if d:
        jobs = [
            ('unpaywall', 'https://api.unpaywall.org/v2/%s?email=%s' %
             (urllib.parse.quote(d, safe=''), urllib.parse.quote(OA_EMAIL))),
            ('openalex', 'https://api.openalex.org/works/https://doi.org/%s?mailto=%s' %
             (urllib.parse.quote(d, safe=''), urllib.parse.quote(OA_EMAIL))),
            ('s2', 'https://api.semanticscholar.org/graph/v1/paper/DOI:%s'
                   '?fields=openAccessPdf,externalIds,url' %
             urllib.parse.quote(d, safe='')),
            ('crossref', 'https://api.crossref.org/works/%s' %
             urllib.parse.quote(d, safe='')),
        ]

    def query(item):
        name, url = item
        try:
            return name, _json_api(url, 5)
        except Exception:
            return name, None

    if jobs:
        pool = ThreadPoolExecutor(max_workers=4)
        futures = [pool.submit(query, j) for j in jobs]
        try:
            for f in as_completed(futures, timeout=6):
                try:
                    name, j = f.result()
                except Exception:
                    continue
                if not j:
                    continue
                if name == 'unpaywall':
                    locs = ([j.get('best_oa_location')] +
                            (j.get('oa_locations') or []))[:8]
                    for loc in locs:
                        if loc:
                            add(loc.get('url_for_pdf'))
                            add(loc.get('url'))
                elif name == 'openalex':
                    best = j.get('best_oa_location') or {}
                    add(best.get('pdf_url'))
                    for loc in (j.get('locations') or [])[:8]:
                        add((loc or {}).get('pdf_url'))
                    add((j.get('open_access') or {}).get('oa_url'))
                elif name == 's2':
                    add((j.get('openAccessPdf') or {}).get('url'))
                    ids = j.get('externalIds') or {}
                    if ids.get('ArXiv'):
                        add('https://arxiv.org/pdf/' + str(ids['ArXiv']))
                elif name == 'crossref':
                    for lk in ((j.get('message') or {}).get('link') or [])[:8]:
                        u = (lk or {}).get('URL') or ''
                        if u and ('pdf' in u.lower() or 'pdf' in str(
                                (lk or {}).get('content-type', '')).lower()):
                            add(u)
        except Exception:
            pass
        finally:
            pool.shutdown(wait=False)

    m = re.search(r'10\.48550/arXiv\.([0-9.]+)', doi or '', re.I)
    if m:
        add('https://arxiv.org/pdf/' + m.group(1))
    m = re.search(r'arxiv\.org/(?:abs|html|pdf)/([0-9.]+(?:v\d+)?)',
                  (target or '') + ' ' + (title or ''), re.I)
    if m:
        aid = m.group(1)
        add('https://arxiv.org/pdf/' + aid)
        add('https://export.arxiv.org/pdf/' + aid)
    with OA_LOCK:
        if len(OA_CACHE) > 400:
            OA_CACHE.clear()
        OA_CACHE[key] = (time.time(), urls[:10])
    return urls[:10]


def _pdf_headers(url, html=False, referer='', cookie=''):
    p = urllib.parse.urlsplit(url)
    origin = p.scheme + '://' + (p.netloc or '')
    h = {
        'User-Agent': BROWSER_UA,
        'Accept': ('text/html,application/xhtml+xml,application/xml;q=0.9,'
                   'image/avif,image/webp,*/*;q=0.8') if html else
                  'application/pdf,application/octet-stream;q=0.9,*/*;q=0.8',
        'Accept-Language': 'en-US,en;q=0.9,zh-CN;q=0.8',
        'Upgrade-Insecure-Requests': '1',
        'Sec-Fetch-Dest': 'document',
        'Sec-Fetch-Mode': 'navigate',
        'Sec-Fetch-Site': 'same-origin',
        'Sec-Fetch-User': '?1',
        'Referer': referer or (origin + '/'),
    }
    if cookie:
        h['Cookie'] = cookie
    return h


def _landing_cookie(url, doi=''):
    """Warm up the article landing page so the PDF retry looks like a browser
    session (cookie + real Referer). Only called after a 401/403/429/503."""
    if doi:
        landing = 'https://doi.org/' + re.sub(
            r'^https?://(?:dx\.)?doi\.org/', '', doi, flags=re.I)
    else:
        low = url.lower()
        p = urllib.parse.urlsplit(url)
        if 'arxiv.org/pdf/' in low:
            landing = url.replace('/pdf/', '/abs/')
        elif '/pdf/' in low:
            landing = url.rsplit('/pdf/', 1)[0]
        elif p.path.lower().endswith('.pdf'):
            landing = urllib.parse.urlunsplit(
                (p.scheme, p.netloc, p.path.rsplit('/', 1)[0] + '/', '', ''))
        else:
            landing = p.scheme + '://' + (p.netloc or '') + '/'
    try:
        req = urllib.request.Request(landing, headers=_pdf_headers(landing, html=True))
        with _open_with_fallback(req, 6) as r:
            r.read(8192)
            vals = r.headers.get_all('Set-Cookie') or []
        cookies = [v.split(';', 1)[0].strip() for v in vals]
        return '; '.join([c for c in cookies if c][:8]), landing
    except Exception:
        return '', landing


def _fetch_one_pdf(url, doi='', timeout=14, max_bytes=64 << 20):
    """Return PDF bytes from one URL, or None. Handles PMC proof-of-work and
    one cookie-warmed retry when the CDN challenges the first request."""
    def once(headers, t):
        req = urllib.request.Request(url, headers=headers)
        deadline = time.time() + t * 1.4
        with _open_with_fallback(req, t, deadline) as r:
            chunks, size = [], 0
            while True:
                if time.time() > deadline:
                    raise urllib.error.URLError('pdf transfer deadline')
                part = r.read(262144)
                if not part:
                    break
                chunks.append(part)
                size += len(part)
                if size >= max_bytes:
                    break
            return b''.join(chunks), (r.headers.get('Content-Type') or '').lower()

    try:
        raw, ctype = once(_pdf_headers(url), timeout)
    except urllib.error.HTTPError as e:
        if e.code not in (401, 403, 429, 503):
            return None
        cookie, referer = _landing_cookie(url, doi)
        if not (cookie or referer):
            return None
        try:
            raw, ctype = once(_pdf_headers(url, referer=referer, cookie=cookie),
                              timeout)
        except Exception:
            return None
    except Exception:
        return None

    if raw[:8].startswith(b'%PDF') or b'%PDF' in raw[:1024]:
        return raw
    text = raw[:8192].decode('utf-8', 'replace')
    if 'POW_CHALLENGE' in text:
        ck = _solve_pmc_pow(text)
        if ck:
            try:
                raw, _ = once(_pdf_headers(url, cookie=ck), timeout)
                if raw[:8].startswith(b'%PDF') or b'%PDF' in raw[:1024]:
                    return raw
            except Exception:
                pass
    return None


def _pdf_candidates(target, doi='', pmcid='', title=''):
    """Ordered list of URLs likely to serve the actual PDF bytes."""
    cands = [target]
    m = re.search(r'arxiv\.org/(?:abs|html)/([0-9.]+(?:v\d+)?)', target, re.I)
    if m:
        aid = m.group(1)
        cands.insert(0, 'https://arxiv.org/pdf/' + aid)
        cands.insert(1, 'https://export.arxiv.org/pdf/' + aid)
    m = re.match(r'https?://(?:www\.)?ncbi\.nlm\.nih\.gov/pmc/articles/(PMC\d+)/pdf/?',
                 target, re.I)
    if m:  # legacy PMC domain -> the working canonical form
        cands.insert(0, 'https://pmc.ncbi.nlm.nih.gov/articles/%s/pdf/' % m.group(1))
    if pmcid and re.match(r'^PMC\d+$', pmcid, re.I):
        u = 'https://pmc.ncbi.nlm.nih.gov/articles/%s/pdf/' % pmcid.upper()
        if u not in cands:
            cands.insert(0, u)
    # A DOI landing URL often serves the PDF once Accept/Referer look normal.
    d = re.sub(r'^https?://(?:dx\.)?doi\.org/', '', (doi or '').strip(),
               flags=re.I).strip()
    if d and 'doi.org/' in target.lower():
        cands.append('https://doi.org/' + d)
    return list(dict.fromkeys(cands))[:4]


def fetch_pdf(target, doi='', pmcid='', title=''):
    """Return real PDF bytes or raise PdfBlocked. Total work is time-bounded so
    a blocked publisher never leaves the reader waiting on a long chain."""
    deadline = time.time() + 10

    def attempt(url, budget):
        left = max(1.0, min(budget, deadline - time.time()))
        return fence(lambda: _fetch_one_pdf(url, doi, left), left + 0.6,
                     None, True)

    # The open-access lookup (Unpaywall / OpenAlex / S2 / Crossref) runs at the
    # same time as the direct candidates. Sequentially it only started after
    # every publisher link had already timed out, which doubled the wait on
    # exactly the papers that need it most.
    oa_box = {'urls': []}
    oa_thread = threading.Thread(
        target=lambda: oa_box.update(
            urls=_collect_oa_urls(doi, title, target)[:4]),
        daemon=True, name='oa-urls')

    def drain_oa():
        if oa_thread.is_alive() or not oa_box['urls']:
            return []
        return list(oa_box['urls'])

    oa_thread.start()
    tried = set()
    for url in _pdf_candidates(target, doi, pmcid, title):
        if time.time() >= deadline:
            break
        tried.add(url)
        raw = attempt(url, 8)
        if raw:
            return raw

    oa_thread.join(max(0.5, min(4.0, deadline - time.time())))
    for url in drain_oa():
        if url in tried or time.time() >= deadline:
            continue
        tried.add(url)
        raw = attempt(url, 5)
        if raw:
            return raw
    # Internal reason only; the route returns a neutral hand-off page instead.
    raise PdfBlocked('PDF 暂时不可读')


# A neutral, branded hand-off card. It silently moves the reader to the full
# web view, so a publisher-side block never appears as an error in the product.
_PDF_FALLBACK_HTML = '''<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<style>
 :root{--brand:#2563eb;--ink:#1f2937;--sub:#6b7280}
 body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;
      background:#f5f7fa;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI","PingFang SC","Microsoft YaHei",sans-serif}
 .card{background:#fff;border:1px solid #e5e7eb;border-radius:14px;
       box-shadow:0 8px 30px rgba(16,24,40,.08);max-width:420px;width:86%;
       padding:32px 34px;text-align:center}
 .mark{width:44px;height:44px;margin:0 auto 16px;border-radius:12px;background:#dbeafe;
       color:var(--brand);font-size:22px;line-height:44px}
 h2{margin:0 0 8px;font-size:17px;color:var(--ink)}
 p{margin:0;font-size:13px;line-height:1.8;color:var(--sub)}
 .bar{height:4px;border-radius:4px;background:#eef2f7;margin:20px 0 0;overflow:hidden}
 .bar i{display:block;height:100%;width:38%;background:var(--brand);border-radius:4px;
        animation:move 1.4s ease-in-out infinite alternate}
 @keyframes move{from{transform:translateX(-30%)}to{transform:translateX(190%)}}
 .row{display:flex;gap:10px;margin-top:22px;justify-content:center;flex-wrap:wrap}
 button{border:1px solid #e5e7eb;background:#fff;color:var(--ink);border-radius:8px;
        padding:9px 16px;font-size:13px;cursor:pointer}
 button.main{background:var(--brand);border-color:var(--brand);color:#fff}
 @media(prefers-reduced-motion:reduce){.bar i{animation:none;width:100%}}
</style></head><body data-loreseek-fallback="1"><div class="card">
 <div class="mark">◈</div>
 <h2>正在为你打开可读版本</h2>
 <p>正在切换至网页全文，稍候即可继续阅读。</p>
 <div class="bar"><i></i></div>
 <div class="row">
  <button class="main" onclick="parent.readerFallbackFromPdf&&parent.readerFallbackFromPdf()">查看网页全文</button>
  <button onclick="window.open(parent.document.getElementById('readerNewWindow').href,'_blank')">访问原文</button>
 </div>
</div><script>
 (function(){
   function go(){try{
     if(parent.readerFallbackFromPdf){parent.readerFallbackFromPdf();return;}
     parent.switchReaderView&&parent.switchReaderView('page');
   }catch(e){}}
   go();setTimeout(go,220);
 })();
</script></body></html>'''


PDF_FAIL_CACHE = {}


def cached_pdf(target, doi='', pmcid='', title=''):
    hit = PDF_CACHE.get(target)
    if hit and time.time() - hit[0] < CACHE_TTL:
        return hit[1]
    # A recently blocked link must not re-run the whole multi-channel probe.
    fail = PDF_FAIL_CACHE.get(target)
    if fail and time.time() - fail < 90:
        raise PdfBlocked('PDF 暂时不可读')
    try:
        raw = fetch_pdf(target, doi, pmcid, title)
    except PdfBlocked:
        PDF_FAIL_CACHE[target] = time.time()
        raise
    if len(PDF_CACHE) >= CACHE_MAX:
        for k in sorted(PDF_CACHE, key=lambda k: PDF_CACHE[k][0])[:4]:
            PDF_CACHE.pop(k, None)
    PDF_CACHE[target] = (time.time(), raw)
    return raw


# ------------------------------------------------------- Chinese -> EN query
# Long / specific terms MUST come first: otherwise "胶囊算法" would be eaten by
# the generic ("算法" -> algorithm) rule and lose its meaning entirely.
CN_MAP = [
    ('通用人工智能', 'artificial general intelligence'),
    ('生成式人工智能', 'generative artificial intelligence'),
    ('大语言模型', 'large language model'), ('大模型', 'large language model'),
    ('胶囊网络', 'capsule network'), ('胶囊算法', 'capsule network algorithm'),
    ('蚁群算法', 'ant colony optimization'), ('遗传算法', 'genetic algorithm'),
    ('粒子群算法', 'particle swarm optimization'), ('图神经网络', 'graph neural network'),
    ('卷积神经网络', 'convolutional neural network'),
    ('深度强化学习', 'deep reinforcement learning'), ('联邦学习', 'federated learning'),
    ('迁移学习', 'transfer learning'), ('对比学习', 'contrastive learning'),
    ('扩散模型', 'diffusion model'), ('Transformer', 'transformer'),
    ('计算机视觉', 'computer vision'), ('自然语言处理', 'natural language processing'),
    ('脑机接口', 'brain computer interface'), ('具身智能', 'embodied AI'),
    ('多模态大模型', 'multimodal large language model'), ('多模态', 'multimodal'),
    ('知识图谱', 'knowledge graph'), ('检索增强', 'retrieval augmented generation'),
    ('人工智能', 'artificial intelligence'), ('机器学习', 'machine learning'),
    ('深度学习', 'deep learning'), ('神经网络', 'neural network'),
    ('强化学习', 'reinforcement learning'), ('智能体', 'AI agent'),
    ('量子计算', 'quantum computing'), ('量子纠缠', 'quantum entanglement'),
    ('量子纠错', 'quantum error correction'), ('量子机器学习', 'quantum machine learning'),
    ('半导体', 'semiconductor'), ('光刻机', 'lithography'),
    ('芯片', 'semiconductor chip'), ('集成电路', 'integrated circuit'),
    ('第三代半导体', 'wide bandgap semiconductor'),
    ('材料科学', 'materials science'), ('纳米材料', 'nanomaterial'),
    ('石墨烯', 'graphene'), ('钙钛矿', 'perovskite'),
    ('固态电池', 'solid state battery'), ('锂电池', 'lithium battery'),
    ('催化剂', 'catalyst'), ('高温超导', 'high temperature superconductor'),
    ('合成生物学', 'synthetic biology'), ('基因编辑', 'CRISPR gene editing'),
    ('基因组', 'genomics'), ('蛋白质结构', 'protein structure'),
    ('药物研发', 'drug discovery'), ('免疫治疗', 'immunotherapy'),
    ('肿瘤', 'cancer'), ('疫苗', 'vaccine'), ('干细胞', 'stem cell'),
    ('类器官', 'organoid'), ('生物信息', 'bioinformatics'),
    ('可控核聚变', 'nuclear fusion'), ('核聚变', 'nuclear fusion'),
    ('可再生能源', 'renewable energy'), ('光伏', 'photovoltaic'),
    ('氢能', 'hydrogen energy'), ('碳中和', 'carbon neutrality'),
    ('气候变化', 'climate change'), ('储能', 'energy storage'),
    ('航天', 'aerospace'), ('天文', 'astronomy'), ('卫星', 'satellite'),
    ('运载火箭', 'rocket'), ('深空探测', 'deep space exploration'),
    ('暗物质', 'dark matter'), ('引力波', 'gravitational wave'),
    ('机器人', 'robotics'), ('自动驾驶', 'autonomous driving'),
    ('区块链', 'blockchain'), ('网络安全', 'cybersecurity'),
    ('边缘计算', 'edge computing'), ('云计算', 'cloud computing'),
    ('分布式系统', 'distributed system'), ('数据库', 'database'),
    ('编译器', 'compiler'), ('操作系统', 'operating system'),
    # generic fallbacks (keep LAST)
    ('算法', 'algorithm'), ('生物', 'biotechnology'), ('基因', 'genomics'),
    ('蛋白质', 'protein'), ('药物', 'drug discovery'), ('医学', 'biomedical'),
    ('能源', 'renewable energy'), ('材料', 'materials science'),
    ('量子', 'quantum computing'), ('论文', 'research'),
]
ABBR = {'ai': 'artificial intelligence', 'llm': 'large language model',
        'rl': 'reinforcement learning', 'cv': 'computer vision',
        'nlp': 'natural language processing', 'ml': 'machine learning',
        'dl': 'deep learning', 'gpt': 'large language model',
        'gnn': 'graph neural network', 'cnn': 'convolutional neural network',
        'rag': 'retrieval augmented generation', 'agi': 'artificial general intelligence',
        'bci': 'brain computer interface', 'crispr': 'CRISPR gene editing',
        'mrna': 'mRNA vaccine', 'qml': 'quantum machine learning',
        'rlhf': 'reinforcement learning from human feedback',
        'moe': 'mixture of experts', 'vit': 'vision transformer'}
STOP = {'and', 'the', 'for', 'with', 'from', 'this', 'that', 'are',
        'was', 'were', 'into', 'using', 'based', 'study', 'science', 'research'}

# Reuse the search dictionary as the quick-read bilingual glossary and let the
# translation helper use the same proxy-aware HTTPS opener as every other call.
quickread.register_terms(CN_MAP, ABBR)
quickread.set_opener(OPENER)


def translate_query(q):
    """Map Chinese / mixed keywords to an English query for the global APIs."""
    q = (q or '').strip()
    if not q or not re.search(r'[\u4e00-\u9fff]', q):
        return q
    parts, rest = [], q
    for cn, en in CN_MAP:
        if cn in rest:
            parts.append(en)
            rest = rest.replace(cn, ' ')
    for tok in re.findall(r'[A-Za-z0-9\-]{2,}', rest):
        parts.append(ABBR.get(tok.lower(), tok))
    return ' '.join(dict.fromkeys(parts)) or q


# Some Chinese words are ambiguous in a Chinese full-text index. "胶囊算法"
# means a Capsule Network algorithm in ML, but a raw Chinese search also hits
# pharmaceutical "胶囊" (capsule pills). Normalise to the standard academic term.
CN_QUERY_FIX = [
    ('胶囊算法', '胶囊网络'),
]


def zh_query_for(raw_q, q_en):
    """Chinese query for the Chinese-literature source (never drops the original)."""
    raw_q = (raw_q or '').strip()
    if re.search(r'[\u4e00-\u9fff]', raw_q):
        for bad, good in CN_QUERY_FIX:
            if bad in raw_q.lower() or bad in raw_q:
                raw_q = raw_q.replace(bad, good)
        return raw_q
    # English input -> derive a Chinese equivalent so Chinese results still sync
    en2cn = {en: cn for cn, en in CN_MAP}
    low = (q_en or raw_q or '').lower()
    hits = [cn for en, cn in en2cn.items() if en in low]
    return ' '.join(dict.fromkeys(hits)) if hits else ''


def arxiv_query(q_en):
    words = [w for w in re.findall(r'[A-Za-z][A-Za-z\-]{2,}', q_en.lower())
             if w not in STOP][:4]
    if not words:
        return 'cat:cs.AI OR cat:cs.LG OR cat:q-bio.* OR cat:quant-ph'
    return ' OR '.join('all:%s' % w for w in words)


# ------------------------------------------------------------------ data sources
ATOM = {'a': 'http://www.w3.org/2005/Atom',
        'arxiv': 'http://arxiv.org/schemas/atom'}


def fetch_arxiv(q_en):
    sq = arxiv_query(q_en)
    url = 'https://export.arxiv.org/api/query?' + urllib.parse.urlencode({
        'search_query': sq, 'start': 0, 'max_results': 14,
        'sortBy': 'submittedDate', 'sortOrder': 'descending'})
    raw = ''
    for attempt in range(2):
        try:
            raw, _ = get(url)
            break
        except urllib.error.HTTPError as e:
            # arXiv frequently answers "429 Rate exceeded." on busy export IPs
            if e.code == 429 and attempt == 0:
                time.sleep(2.0)
                continue
            raise
    root = ET.fromstring(raw)
    out = []
    for e in root.findall('a:entry', ATOM):
        def t(path):
            n = e.find(path, ATOM)
            return (n.text or '').strip().replace('\n', ' ') if n is not None else ''
        abs_url = t('a:id')
        pdf = ''
        for l in e.findall('a:link', ATOM):
            if l.get('title') == 'pdf':
                pdf = l.get('href', '')
        authors = [n.text.strip() for n in e.findall('a:author/a:name', ATOM) if n.text]
        aid = abs_url.rsplit('/abs/', 1)[-1]
        out.append({
            'source': 'arxiv', 'title': t('a:title'), 'abstract': t('a:summary'),
            'url': abs_url, 'pdfUrl': pdf or ('https://arxiv.org/pdf/' + aid),
            'date': t('a:published'), 'authors': authors[:5], 'journal': 'arXiv',
            'doi': '', 'pmid': '', 'pmcid': '', 'isOA': True,
            'freePreviewUrl': pdf or ('https://arxiv.org/pdf/' + aid),
            'arxivId': aid,
        })
    return out


def fetch_pubmed(q_en):
    term = q_en or 'biomedical innovation'
    u1 = 'https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?' + urllib.parse.urlencode(
        {'db': 'pubmed', 'term': term, 'retmax': 12, 'sort': 'date', 'retmode': 'json'})
    d1 = json.loads(get(u1)[0])
    ids = d1.get('esearchresult', {}).get('idlist', [])
    if not ids:
        return []
    u2 = 'https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?' + urllib.parse.urlencode(
        {'db': 'pubmed', 'id': ','.join(ids), 'retmode': 'json'})
    res = json.loads(get(u2)[0]).get('result', {})
    out = []
    for uid in res.get('uids', []):
        it = res.get(uid, {})
        aids = {a.get('idtype'): a.get('value') for a in it.get('articleids', [])}
        pmcid = aids.get('pmc', '')
        out.append({
            'source': 'pubmed', 'title': it.get('title', ''),
            'abstract': '', 'url': 'https://pubmed.ncbi.nlm.nih.gov/%s/' % uid,
            'pdfUrl': ('https://www.ncbi.nlm.nih.gov/pmc/articles/%s/pdf/' % pmcid) if pmcid else '',
            'date': it.get('pubdate', ''),
            'authors': [a.get('name', '') for a in it.get('authors', [])][:5],
            'journal': it.get('fulljournalname') or it.get('source', ''),
            'doi': aids.get('doi', ''), 'pmid': uid, 'pmcid': pmcid,
            'isOA': bool(pmcid),
            'freePreviewUrl': ('https://www.ncbi.nlm.nih.gov/pmc/articles/%s/' % pmcid) if pmcid else '',
        })
    return [x for x in out if x['title']]


def rebuild_abstract(inv):
    if not inv:
        return ''
    pos = []
    for word, idxs in inv.items():
        for i in idxs:
            pos.append((i, word))
    pos.sort(key=lambda x: x[0])
    return ' '.join(w for _, w in pos)


def scholar_link(title):
    """Direct Google Scholar search URL for a paper title / keyword."""
    return 'https://scholar.google.com/scholar?q=' + urllib.parse.quote(title or '')


# One search fires three OpenAlex calls (global / Chinese / Scholar). Firing
# them together trips OpenAlex's 429. More importantly, OpenAlex now enforces a
# *shared free daily budget per IP*: once it is exhausted (HTTP 429
# "Insufficient budget ... $0 remaining, resets at midnight UTC"), every call
# fails until the next UTC day. Retrying is pointless, so we detect that exact
# case, stop hammering it for 10 minutes, and let Crossref carry the two new
# tabs. A free personal API key (env OPENALEX_API_KEY) restores full data.
OPENALEX_KEY = os.environ.get('OPENALEX_API_KEY', '').strip()
_OA_LOCK = threading.Lock()
_OA_BLOCK_UNTIL = 0.0
_OA_BLOCK_REASON = ''


def openalex_available():
    return time.time() >= _OA_BLOCK_UNTIL


def openalex_status():
    return '' if openalex_available() else (_OA_BLOCK_REASON or 'OpenAlex temporarily unavailable')


def openalex_get(url):
    global _OA_BLOCK_UNTIL, _OA_BLOCK_REASON
    if not openalex_available():
        raise RuntimeError(_OA_BLOCK_REASON or 'OpenAlex temporarily unavailable')
    req_url = url
    if OPENALEX_KEY:
        req_url += ('&' if '?' in req_url else '?') + 'api_key=' + urllib.parse.quote(OPENALEX_KEY)
    with _OA_LOCK:
        if not openalex_available():
            raise RuntimeError(_OA_BLOCK_REASON or 'OpenAlex temporarily unavailable')
        for attempt in range(2):
            try:
                data = json.loads(get(req_url)[0])
                time.sleep(0.2)  # polite gap between back-to-back calls
                return data
            except urllib.error.HTTPError as e:
                body = b''
                try:
                    body = e.read()
                except Exception:
                    pass
                if e.code == 429 and (b'Insufficient budget' in body or b'daily budget' in body):
                    _OA_BLOCK_REASON = 'OpenAlex 免费每日配额已耗尽（共享 IP，UTC 0 点重置）'
                    _OA_BLOCK_UNTIL = time.time() + 600  # re-probe after 10 min
                    raise RuntimeError(_OA_BLOCK_REASON)
                if e.code in (429, 500, 502, 503, 504) and attempt == 0:
                    time.sleep(1.5)
                    continue
                raise
        raise RuntimeError('OpenAlex request failed')


def fetch_openalex(q_en, source='openalex', sort=None, per_page=15, page=1):
    """Reusable OpenAlex worker. `source` lets the same index back several tabs
    (global / Chinese / Scholar-style) without duplicating parsing logic.
    `page` is 1-based and powers the Scholar tab's pagination when the
    Google-Scholar channels are unreachable."""
    params = {'search': q_en or 'frontier technology', 'per_page': per_page,
              'page': max(1, int(page or 1)),
              'select': 'id,title,publication_year,doi,cited_by_count,open_access,'
                        'authorships,primary_location,best_oa_location,abstract_inverted_index'}
    if sort:
        params['sort'] = sort
    url = 'https://api.openalex.org/works?' + urllib.parse.urlencode(params)
    data = openalex_get(url)
    out = []
    for it in data.get('results', []):
        oa = it.get('open_access') or {}
        best = it.get('best_oa_location') or {}
        prim = it.get('primary_location') or {}
        doi = (it.get('doi') or '').replace('https://doi.org/', '')
        pdf = best.get('pdf_url') or ''
        title = it.get('title', '')
        out.append({
            'source': source, 'citedBy': it.get('cited_by_count') or 0, 'title': title,
            'abstract': rebuild_abstract(it.get('abstract_inverted_index')),
            'url': ('https://doi.org/' + doi) if doi else (prim.get('landing_page_url') or it.get('id', '')),
            'pdfUrl': pdf,
            'date': str(it.get('publication_year') or ''),
            'authors': [a.get('author', {}).get('display_name', '')
                        for a in (it.get('authorships') or [])][:5],
            'journal': (prim.get('source') or {}).get('display_name', ''),
            'doi': doi, 'pmid': '', 'pmcid': '',
            'isOA': bool(oa.get('is_oa')),
            'oaStatus': oa.get('oa_status', ''),
            'freePreviewUrl': oa.get('oa_url') or best.get('landing_page_url') or pdf,
            'scholarUrl': scholar_link(title),
        })
    return [x for x in out if x['title']]


def fetch_crossref(q_en, source='crossref', rows=12, offset=0):
    # Crossref's `select` parameter silently drops `is-referenced-by-count`,
    # so take the full (small) record: the Scholar view needs real citation
    # counts when OpenAlex's daily budget is exhausted.
    # `mailto` puts us in Crossref's polite pool -> fewer 429s.
    params = {'query': q_en or 'frontier technology', 'rows': rows,
              'offset': max(0, int(offset or 0)),
              'mailto': os.environ.get('LORESEEK_EMAIL', 'contact@loreseek.cn')}
    url = 'https://api.crossref.org/works?' + urllib.parse.urlencode(params)
    data = None
    for attempt in range(4):
        try:
            data = json.loads(get(url)[0])
            break
        except urllib.error.HTTPError as e:
            if e.code in (429, 500, 502, 503, 504) and attempt < 3:
                time.sleep(1.2 * (attempt + 1))
                continue
            raise
        except Exception:
            if attempt < 3:
                time.sleep(0.8 * (attempt + 1))
                continue
            raise
    if data is None:
        return []
    out = []
    for it in data.get('message', {}).get('items', []):
        title = (it.get('title') or [''])[0]
        if not title:
            continue
        dp = (it.get('published') or {}).get('date-parts', [[]])[0]
        doi = it.get('DOI', '')
        out.append({
            'source': source, 'title': title,
            'citedBy': it.get('is-referenced-by-count') or 0,
            'abstract': html_to_text(it.get('abstract') or '', 800),
            'url': it.get('URL') or ('https://doi.org/' + doi),
            'pdfUrl': '', 'date': '-'.join(str(x) for x in dp),
            'authors': [('%s %s' % (a.get('given', ''), a.get('family', ''))).strip()
                        for a in (it.get('author') or [])][:5],
            'journal': (it.get('container-title') or [''])[0],
            'doi': doi, 'pmid': '', 'pmcid': '', 'isOA': False,
            'freePreviewUrl': '', 'scholarUrl': scholar_link(title),
        })
    return out


def fetch_hn(q_en):
    params = {'query': q_en or 'AI', 'tags': 'story', 'hitsPerPage': 12} if q_en else \
             {'tags': 'front_page', 'hitsPerPage': 12}
    url = 'https://hn.algolia.com/api/v1/search?' + urllib.parse.urlencode(params)
    data = json.loads(get(url, timeout=10)[0])
    out = []
    for h in data.get('hits', []):
        out.append({
            'source': 'hn', 'title': h.get('title') or h.get('story_title') or '',
            'abstract': html_to_text(h.get('story_text') or '', 400),
            'url': h.get('url') or ('https://news.ycombinator.com/item?id=%s' % h.get('objectID')),
            'pdfUrl': '', 'date': h.get('created_at', ''),
            'authors': [h.get('author', '')], 'journal': 'Hacker News',
            'doi': '', 'pmid': '', 'pmcid': '', 'isOA': False, 'freePreviewUrl': '',
            'points': h.get('points') or 0, 'comments': h.get('num_comments') or 0,
        })
    return [x for x in out if x['title']]


def fetch_rss(feed_url, source, label):
    proxy = 'https://api.rss2json.com/v1/api.json?' + urllib.parse.urlencode({'rss_url': feed_url})
    data = json.loads(get(proxy, timeout=12)[0])
    out = []
    for it in (data.get('items') or [])[:10]:
        out.append({
            'source': source, 'title': it.get('title', ''),
            'abstract': html_to_text(it.get('description') or it.get('content') or '', 500),
            'url': it.get('link', ''), 'pdfUrl': '', 'date': it.get('pubDate', ''),
            'authors': [it.get('author') or label], 'journal': label,
            'doi': '', 'pmid': '', 'pmcid': '', 'isOA': False, 'freePreviewUrl': '',
        })
    return [x for x in out if x['title']]


# --------------------------------------------- Chinese & Scholar-style views
CJK = re.compile(r'[\u4e00-\u9fff]')


def fetch_chinese(zh_q, raw_q, q_en):
    """Sync *Chinese-language* literature alongside the English results.

    OpenAlex indexes many Chinese journal articles under their original Chinese
    titles, so a Chinese query returns genuinely Chinese papers rather than
    machine-translated English ones. Crossref is a second index; only records
    whose title really contains CJK characters are kept. Chinese databases with
    no public search API are appended as clearly-labelled direct-search entries.
    """
    term = zh_q or raw_q or q_en or '前沿科技'
    # Two independent indexes, queried together: run back to back they cost
    # the sum of both (11s+ measured), concurrently only the slower one.
    got = {}
    pool = ThreadPoolExecutor(max_workers=2)
    futs = {}
    try:
        futs['oa'] = pool.submit(
            fence, lambda: fetch_openalex(term, source='cn', per_page=15),
            6.0, None, True)
        # Crossref has no daily quota, so it is the stable Chinese fallback.
        futs['cr'] = pool.submit(
            fence, lambda: fetch_crossref(term, source='cn', rows=18),
            6.0, None, True)
        for f in as_completed(list(futs.values()), timeout=7.0):
            for k, v in futs.items():
                if v is f:
                    got[k] = f.result() or []
    except Exception:
        pass
    finally:
        pool.shutdown(wait=False)
        for f in futs.values():
            f.cancel()

    out = list(got.get('oa') or [])
    cr = list(got.get('cr') or [])
    # Keep every hit but rank genuine Chinese-language titles first.
    cr.sort(key=lambda x: 0 if CJK.search(x['title']) else 1)
    out += cr

    seen, uniq = set(), []
    for x in out:
        key = re.sub(r'\W+', '', x['title']).lower()
        if key and key not in seen:
            seen.add(key)
            x['scholarUrl'] = scholar_link(x['title'])
            x['lang'] = 'zh'
            uniq.append(x)

    cn_key = urllib.parse.quote(term)
    for name, url, tip in [
        ('中国知网 CNKI', 'https://kns.cnki.net/kns8s/defaultresult/index?kw=' + cn_key,
         '中文期刊 / 学位论文 / 会议论文全文库；全文通常需机构或学校 VPN 权限'),
        ('万方数据', 'https://s.wanfangdata.com.cn/paper?q=' + cn_key,
         '中文期刊、学位论文与会议论文检索'),
        ('维普期刊', 'http://qikan.cqvip.com/Qikan/Search/Index?key=A%3D' + cn_key,
         '中文科技期刊全文数据库'),
        ('百度学术', 'https://xueshu.baidu.com/s?wd=' + cn_key,
         '中文学术搜索，可辅助定位免费全文版本'),
        ('国家哲学社会科学文献中心', 'https://www.ncpssd.org/',
         '国家提供的合法免费中文文献平台'),
    ]:
        uniq.append({
            'source': 'cn', 'title': '🔎 在「%s」检索「%s」' % (name, term),
            'abstract': tip, 'url': url, 'pdfUrl': '', 'date': '',
            'authors': [], 'journal': name, 'doi': '', 'pmid': '', 'pmcid': '',
            'isOA': False, 'freePreviewUrl': '', 'entryLink': True,
            'scholarUrl': scholar_link(term), 'lang': 'zh',
        })
    papers = [x for x in uniq if not x.get('entryLink')]
    entries = [x for x in uniq if x.get('entryLink')]

    # Re-rank so papers containing the *whole* Chinese term come first. Without
    # this, a query like 胶囊网络 also surfaces pharmaceutical 「胶囊」papers on top.
    def rank(x):
        t = x.get('title', '')
        if term in t:
            return 0
        if CJK.search(t):
            return 1
        return 2

    papers.sort(key=rank)
    return papers[:25] + entries


# ------------------------------------------------------- Google Scholar channels
# Google Scholar itself has no free official API, but its result pages are
# plain HTML that a number of public mirror stations re-serve verbatim. We
# therefore try, in order:
#   1. the official scholar.google.com (+ .hk) — works whenever a VPN/proxy is on;
#   2. well-known mirror channels (谷粉学术 / 懒人学术 etc.) — same markup,
#      reachable directly from CN networks; some now require login or show a
#      captcha, in which case parsing finds no results and we simply move on;
#   3. an OpenAlex + Crossref aggregate with identical pagination semantics
#      (labelled honestly in the UI as an aggregate fallback).
# The first channel that yields parseable results is remembered, so flipping
# pages does not re-probe dead hosts every time.
_SCHOLAR_MIRROR_ENV = os.environ.get('LORESEEK_SCHOLAR_MIRROR') or ''
SCHOLAR_HOSTS = [
    h for h in ([_SCHOLAR_MIRROR_ENV.rstrip('/')] if _SCHOLAR_MIRROR_ENV else []) +
    ['https://scholar.google.com', 'https://scholar.google.com.hk',
     'https://scholar.lanfanshu.cn', 'https://xueshu.lanfanshu.cn']
    if h
]
# Hosts known to be SPA/verify-gated (a JSON shell, never plain GS markup):
# kept out of the list above so the probe stays fast.
SCHOLAR_BAD_UNTIL = {}          # host -> monotonic ts until which we skip it
SCHOLAR_GOOD_HOST = None        # last channel that produced real results
SCHOLAR_CACHE = {}              # (q.lower(), start) -> (ts, payload)
SCHOLAR_LOCK = threading.Lock()
SCHOLAR_TTL = 600               # 10 min, mirrors are slow and rate-limited
# Hard wall-clock budgets. Without a VPN the official channels can only be
# discovered dead by waiting, so the race — and the aggregate that replaces
# it — must both be bounded, otherwise one dead host sets the page's speed.
SCHOLAR_PROBE_BUDGET = 5.0
SCHOLAR_AGG_BUDGET = 6.0
SCHOLAR_PARK_SECS = 900         # stop re-probing a silent channel for 15 min

_GS_TITLE = re.compile(r'<h3 class="gs_rt"[^>]*>(.*?)</h3>', re.S)
_GS_META = re.compile(r'<div class="gs_a"[^>]*>(.*?)</div>', re.S)
_GS_SNIPPET = re.compile(r'<div class="gs_rs"[^>]*>(.*?)</div>', re.S)
_GS_SIDE = re.compile(r'<div class="gs_or_ggsm"[^>]*>\s*<a[^>]+href="([^"]+)"'
                      r'[^>]*>(.*?)</a>', re.S)
_GS_CITED = re.compile(r'>(?:被引用次数[：:]\s*|Cited by\s*)([\d,]+)')
_GS_VERSIONS = re.compile(r'>(?:All\s+(\d+)\s+versions|全部\s*(\d+)\s*个版本)')
_GS_TOTAL = re.compile(r'(?:约\s*|About\s+)([\d,\.]+)\s*(?:条结果|results)')
_GS_NEXT = re.compile(r'>\s*(?:下一页|Next)\s*<', re.I)
_GS_CAPTCHA = re.compile(r'gs_captcha|unusual traffic|并非计算机|不是计算机程序',
                         re.I)
_TAG = re.compile(r'<[^>]+>')


def _gs_clean(raw):
    """Strip tags but KEEP <b> highlights (Scholar bolds query terms)."""
    raw = raw.replace('<b>', '\x01').replace('</b>', '\x02')
    raw = _TAG.sub('', raw)
    return (raw.replace('\x01', '<b>').replace('\x02', '</b>')
               .replace('&quot;', '"').replace('&#39;', "'")
               .replace('&amp;', '&').replace('&lt;', '<').replace('&gt;', '>')
               .replace('&nbsp;', ' ')).strip()


def parse_scholar_html(html, host):
    """Extract the ten result blocks of a Google-Scholar-shaped page.
    Works for the official site and for any mirror re-serving its markup."""
    if _GS_CAPTCHA.search(html):
        raise RuntimeError('captcha')
    if 'class="gs_ri"' not in html:
        raise RuntimeError('no result blocks (login wall / SPA shell)')
    blocks = html.split('<div class="gs_r gs_or gs_scl')[1:]
    items = []
    for seg in blocks:
        # The last segment runs to the end of the document (footer scripts,
        # injected mirror JS) — cut it where the real block content ends.
        seg = seg.split('<div id="gs_res_ccl_bot')[0].split('<script')[0]
        tm = _GS_TITLE.search(seg)
        if not tm:
            continue
        anchor = re.search(r'<a[^>]+href="([^"]+)"[^>]*>(.*?)</a>', tm.group(1),
                           re.S)
        title = _gs_clean(tm.group(1))
        title = re.sub(r'^\[(PDF|HTML|DOC|BOOK)\]\s*', '', title, flags=re.I)
        if not title:
            continue
        link = anchor.group(1) if anchor else ''
        if link.startswith('/'):
            link = host + link
        meta = _gs_clean(_GS_META.search(seg).group(1)) if _GS_META.search(seg) else ''
        authors, journal, year = '', '', ''
        if meta:
            parts = re.split(r'\s+-\s+', meta)
            authors = parts[0] if parts else ''
            if len(parts) >= 2:
                journal = parts[1].split(',')[0].strip()
            ym = re.search(r'((?:19|20)\d{2})', meta)
            if ym:
                year = ym.group(1)
        sn = _GS_SNIPPET.search(seg)
        snippet = _gs_clean(sn.group(1))[:600] if sn else ''
        cited = 0
        cm = _GS_CITED.search(seg)
        if cm:
            cited = int(cm.group(1).replace(',', ''))
        pdf, side = '', ''
        for sm in _GS_SIDE.finditer(seg):
            href, text = sm.group(1), _TAG.sub('', sm.group(2)).strip()
            if href.startswith('/'):
                href = host + href
            if not side:
                side = href
            low = text.lower()
            if not pdf and ('[pdf' in low or 'pdf' in low and href.lower().endswith('.pdf')):
                pdf = href
        vm = _GS_VERSIONS.search(seg)
        versions = int(vm.group(1) or vm.group(2)) if vm else 0
        related = ''
        rm = re.search(r'href="(/scholar\?q=related:[^"]+)"', seg)
        if rm:
            related = host + rm.group(1).replace('&amp;', '&')
        cluster = ''
        km = re.search(r'href="(/scholar\?[^"]*cluster=[^"]+)"', seg)
        if km:
            cluster = host + km.group(1).replace('&amp;', '&')
        items.append({
            'source': 'scholar', 'title': title, 'abstract': snippet,
            'url': link or related or cluster,
            'pdfUrl': pdf, 'freePreviewUrl': pdf or side,
            'date': year,
            'authors': [a.strip() for a in re.split(r'[,，…]', authors) if a.strip()][:5],
            'journal': journal, 'doi': '', 'pmid': '', 'pmcid': '',
            'isOA': bool(pdf), 'citedBy': cited,
            'citedByLabel': ('被引用次数：' + format(cited, ',')) if cited else '',
            'versions': versions, 'relatedUrl': related, 'versionsUrl': cluster,
            'host': host,
            'lang': 'zh' if CJK.search(title) else 'en',
        })
    return items


def _scholar_fetch_host(host, q, start):
    """Fetch one page from one channel; raises on anything unparseable."""
    url = (host + '/scholar?' + urllib.parse.urlencode(
        {'q': q, 'hl': 'zh-CN', 'start': start, 'num': 10}))
    raw = get(url, timeout=6 if 'google.com' in host else 9)[0]
    html = raw.decode('utf-8', 'ignore') if isinstance(raw, (bytes,
                                                             bytearray)) else str(raw)
    items = parse_scholar_html(html, host)
    if not items:
        raise RuntimeError('empty page')
    total = None
    tm = _GS_TOTAL.search(html)
    if tm:
        try:
            total = int(tm.group(1).replace(',', '').replace('.', ''))
        except ValueError:
            total = None
    return items, total, bool(_GS_NEXT.search(html))


def _scholar_cooldown(host, sec=600):
    with SCHOLAR_LOCK:
        SCHOLAR_BAD_UNTIL[host] = time.time() + sec


def _scholar_probe(hosts, q, start, budget):
    """Race the channels and return the first parseable page inside `budget`.

    Each worker is individually fenced, and the pool is abandoned rather than
    awaited, so a channel that never answers costs `budget` — not its own
    connect timeout multiplied by every retry.
    """
    if not hosts:
        return None, []
    winner, errs = None, []
    pool = ThreadPoolExecutor(max_workers=min(4, len(hosts)))
    futs = {}
    for h in hosts:
        futs[pool.submit(fence,
                         lambda h=h: _scholar_fetch_host(h, q, start),
                         6.0, None, True)] = h
    try:
        for f in as_completed(futs, timeout=budget):
            host = futs[f]
            res = f.result()
            if res:
                winner = (host,) + res
                break
            errs.append(urllib.parse.urlsplit(host).hostname or host)
    except Exception:               # nothing answered inside the budget
        errs.append('timeout')
    finally:
        pool.shutdown(wait=False)
        for f in futs:
            f.cancel()

    with SCHOLAR_LOCK:
        if winner:
            for host in futs.values():          # losers are just slower, not dead
                if host != winner[0]:
                    SCHOLAR_BAD_UNTIL[host] = time.time() + 120
        else:
            # Every unanswered channel is parked, so turning a page does not
            # spend the same budget rediscovering that they are dark.
            for host in futs.values():
                SCHOLAR_BAD_UNTIL[host] = time.time() + SCHOLAR_PARK_SECS
    return winner, errs


def _scholar_aggregate_begin(q, start):
    """Start the OpenAlex + Crossref page fetch in the background.

    It runs alongside the mirror probe, so whichever answers first is ready:
    when a mirror works the indexes merely warm their own caches, and when
    every mirror is dark the fallback is already done instead of adding
    another 2-3 s on top of the failed probe.
    """
    q_en = translate_query(q) or q
    pool = ThreadPoolExecutor(max_workers=2)
    futs = [
        pool.submit(fence,
                    lambda: fetch_openalex(q_en, source='scholar', per_page=10,
                                           page=start // 10 + 1),
                    7.0, None, True),
        pool.submit(fence,
                    lambda: fetch_crossref(q_en, source='scholar', rows=10,
                                           offset=start),
                    7.0, None, True),
    ]
    return {'pool': pool, 'futs': futs, 'bonus': []}


def _scholar_aggregate_join(agg, budget):
    merged = list(agg.get('bonus') or [])
    try:
        for f in as_completed(agg['futs'], timeout=budget):
            merged += f.result() or []
    except Exception:
        pass
    finally:
        agg['pool'].shutdown(wait=False)
        for f in agg['futs']:
            f.cancel()
    return merged


def scholar_payload(q, start=0, allow_fallback=True):
    """One Scholar-tab page through the channel chain, with caching."""
    q = (q or '').strip() or 'frontier technology'
    start = max(0, int(start or 0))
    key = (q.lower(), start)
    with SCHOLAR_LOCK:
        hit = SCHOLAR_CACHE.get(key)
        if hit and time.time() - hit[0] < SCHOLAR_TTL:
            return hit[1]

    global SCHOLAR_GOOD_HOST
    hosts = list(SCHOLAR_HOSTS)
    good = SCHOLAR_GOOD_HOST
    if good in hosts:
        hosts.remove(good)
        hosts.insert(0, good)         # the proven channel goes first
    live = []
    with SCHOLAR_LOCK:
        for host in hosts:
            until = SCHOLAR_BAD_UNTIL.get(host, 0)
            if not (until and time.time() < until):
                live.append(host)
    if not live:
        # Everything got parked: re-open the probe instead of reporting empty.
        live = hosts

    # ---- aggregate fallback: same pagination semantics, honest labelling ----
    # Both indexes are queried at once, and started in parallel with the
    # channel probe: serially they cost ~8s, and only after a 5s wait.
    agg = _scholar_aggregate_begin(q, start) if allow_fallback else None

    winner, errs = _scholar_probe(live, q, start, SCHOLAR_PROBE_BUDGET)
    if winner:
        host, items, total, has_next = winner
        with SCHOLAR_LOCK:
            SCHOLAR_GOOD_HOST = host
            SCHOLAR_BAD_UNTIL.pop(host, None)
        payload = {
            'ok': True, 'channel': ('official' if 'google.com' in host
                                    else 'mirror'),
            'host': host, 'q': q, 'start': start, 'items': items,
            'total': total, 'pageSize': 10,
            'hasNext': has_next if total is None else start + 10 < total,
            'hasPrev': start > 0,
            'note': ('全球学术索引 · 官方通道' if 'google.com' in host
                     else '全球学术索引 · 聚合通道'),
        }
        with SCHOLAR_LOCK:
            if len(SCHOLAR_CACHE) > 120:
                SCHOLAR_CACHE.clear()
            SCHOLAR_CACHE[key] = (time.time(), payload)
        if agg:                     # the mirror won: drop the standby work
            agg['pool'].shutdown(wait=False)
            for f in agg['futs']:
                f.cancel()
        return payload

    # The literature feed already carries OpenAlex + Crossref results, so the
    # main search can simply re-label those instead of paying for a duplicate
    # round of index requests.
    if not allow_fallback:
        return {'ok': False, 'channel': 'none', 'host': '', 'q': q,
                'start': start, 'items': [], 'total': None, 'pageSize': 10,
                'hasNext': False, 'hasPrev': start > 0, 'note': ''}

    # ---- aggregate fallback result, collected from the already-running job ----
    merged = _scholar_aggregate_join(agg, SCHOLAR_AGG_BUDGET) if agg else []
    seen, uniq = set(), []
    for x in merged:
        k = re.sub(r'\W+', '', x['title']).lower()
        if k and k not in seen:
            seen.add(k)
            x['source'] = 'scholar'
            x['scholarUrl'] = scholar_link(x['title'])
            x['lang'] = 'zh' if CJK.search(x['title']) else 'en'
            if x.get('citedBy'):
                x['citedByLabel'] = '被引用次数：%s' % format(x['citedBy'], ',')
            uniq.append(x)
    uniq.sort(key=lambda x: x.get('citedBy') or 0, reverse=True)
    payload = {
        'ok': bool(uniq), 'channel': 'aggregate', 'host': '', 'q': q,
        'start': start, 'items': uniq[:10], 'total': None, 'pageSize': 10,
        'hasNext': len(uniq) >= 10, 'hasPrev': start > 0,
        'note': '已为你聚合开放学术索引结果',
    }
    with SCHOLAR_LOCK:
        if uniq:
            SCHOLAR_CACHE[key] = (time.time(), payload)
    return payload


def do_scholar_search(qs):
    p = scholar_payload(qs.get('q', ''), qs.get('start', 0))
    return p


def fetch_scholar_like(q_en, zh_q):
    """The Scholar job of the main streaming search = page 0 of the same
    channel chain used by the dedicated paginated Scholar tab.

    The aggregate fallback is deliberately skipped here: OpenAlex and Crossref
    are already separate jobs of this same search, so `search_scholar_fallback`
    can re-label their real records for free instead of requesting them twice.
    """
    p = scholar_payload(q_en or zh_q or 'frontier technology', 0,
                        allow_fallback=False)
    out = list(p.get('items') or [])
    for x in out:
        x['scholarUrl'] = x.get('relatedUrl') or x.get('versionsUrl') or \
            scholar_link(x['title'])
    key = urllib.parse.quote(q_en or zh_q or 'frontier technology')
    host = p.get('host') or SCHOLAR_HOSTS[0]
    out.append({
        'source': 'scholar',
        'title': '🎓 在 Google Scholar 中分页检索「%s」' % (q_en or zh_q or '前沿科技'),
        'abstract': '在 Google Scholar 中继续浏览完整检索结果。',
        'url': host + '/scholar?q=' + key + '&hl=zh-CN',
        'pdfUrl': '', 'date': '', 'authors': [], 'journal': 'Google Scholar',
        'doi': '', 'pmid': '', 'pmcid': '', 'isOA': False,
        'freePreviewUrl': '', 'entryLink': True,
        'scholarUrl': host + '/scholar?q=' + key + '&hl=zh-CN',
    })
    return out


SOURCES = {
    'arxiv': lambda q: fetch_arxiv(q),
    'pubmed': lambda q: fetch_pubmed(q),
    'openalex': lambda q: fetch_openalex(q),
    'crossref': lambda q: fetch_crossref(q),
    'hn': lambda q: fetch_hn(q),
    'nature': lambda q: fetch_rss('https://www.nature.com/nature.rss', 'nature', 'Nature'),
    'techcrunch': lambda q: fetch_rss('https://techcrunch.com/feed/', 'techcrunch', 'TechCrunch'),
}


# ===========================================================================
# 全球热点 / Global hotspots — a DELIBERATELY SEPARATE data pipeline.
#
# This is real-time tech NEWS + community buzz + freshly-trending projects.
# It never enters allItems / SOURCES, never joins the literature search, and
# never touches the paper feed's filters, pagination or MT queue. Feeds are
# fetched as raw XML directly: the free rss2json proxy returns HTTP 429 as soon
# as several channels are requested concurrently, which is exactly our case.
# ===========================================================================
import email.utils as _maildate
import datetime as _dt

HOT_RSS = [
    ('techcrunch', 'TechCrunch', 'https://techcrunch.com/feed/', '#ff6b35'),
    ('theverge', 'The Verge', 'https://www.theverge.com/rss/index.xml', '#8b5cf6'),
    ('wired', 'WIRED', 'https://www.wired.com/feed/rss', '#e11d48'),
    ('mit', 'MIT Tech Review', 'https://www.technologyreview.com/feed/', '#dc2626'),
    ('solidot', 'Solidot', 'https://www.solidot.org/index.rss', '#0d9488'),
    ('scidaily', 'ScienceDaily', 'https://www.sciencedaily.com/rss/top/technology.xml', '#059669'),
    ('physorg', 'Phys.org', 'https://phys.org/rss-feed/technology-news/', '#4f46e5'),
]

HOT_CATS = [
    ('ai', 'AI · 大模型', '#8b5cf6',
     ('ai', 'artificial intelligence', 'llm', 'gpt', 'openai', 'chatgpt', 'gemini',
      'claude', 'anthropic', 'deepmind', 'neural', 'machine learning', 'generative',
      'transformer', 'diffusion', '智能体', '大模型', '人工智能', '深度学习', '模型')),
    ('chip', '芯片 · 算力', '#f59e0b',
     ('chip', 'semiconductor', 'nvidia', 'gpu', 'tsmc', 'intel', 'amd', 'wafer',
      'lithography', 'processor', 'hbm', 'asml', '芯片', '半导体', '算力', '光刻')),
    ('quantum', '量子计算', '#6366f1', ('quantum', 'qubit', '量子')),
    ('space', '航天 · 太空', '#3b82f6',
     ('space', 'nasa', 'spacex', 'rocket', 'satellite', 'mars', 'moon', 'orbit',
      'telescope', 'starship', '航天', '火箭', '卫星', '太空')),
    ('bio', '生物 · 医疗', '#10b981',
     ('crispr', 'gene', 'genome', 'protein', 'drug', 'vaccine', 'dna', 'biotech',
      'clinical', 'cancer', 'mrna', '生物', '基因', '蛋白', '细胞', '疫苗')),
    ('energy', '能源 · 环境', '#ef4444',
     ('fusion', 'battery', 'solar', 'reactor', 'nuclear', 'climate', 'carbon',
      'energy', '核聚变', '电池', '光伏', '能源')),
    ('robot', '机器人', '#ec4899',
     ('robot', 'humanoid', 'autonomous', 'self-driving', 'drone', '机器人', '自动驾驶', '无人机')),
    ('policy', '安全 · 政策', '#64748b',
     ('security', 'cyber', 'hack', 'privacy', 'regulation', 'antitrust', 'lawsuit',
      'export control', '监管', '禁令', '诉讼', '安全')),
]


def hot_classify(text):
    s = (text or '').lower()
    best = None
    for cat, label, color, words in HOT_CATS:
        hits = 0
        for w in words:
            if len(w) <= 3 and re.fullmatch(r'[a-z]+', w):
                hits += len(re.findall(r'\b' + re.escape(w) + r'\b', s))
            elif w in s:
                hits += 1
        if hits and (best is None or hits > best[0]):
            best = (hits, cat, label, color)
    return best[1:] if best else ('frontier', '前沿综合', '#0ea5e9')


def _hot_time(s):
    """Parse an RSS / Atom / ISO date into epoch seconds; 0 when unknown."""
    if not s:
        return 0.0
    s = s.strip()
    try:
        d = _maildate.parsedate_to_datetime(s)
        if d:
            if d.tzinfo is None:
                d = d.replace(tzinfo=_dt.timezone.utc)
            return float(d.timestamp())
    except Exception:
        pass
    try:
        d = _dt.datetime.fromisoformat(s.replace('Z', '+00:00'))
        if d.tzinfo is None:
            d = d.replace(tzinfo=_dt.timezone.utc)
        return float(d.timestamp())
    except Exception:
        pass
    return 0.0


def _rss_items(raw):
    """Tolerant RSS 2.0 / RDF / Atom parser — namespace-agnostic."""
    try:
        root = ET.fromstring(raw)
    except Exception:
        try:
            root = ET.fromstring(raw.encode('utf-8', 'ignore').decode('utf-8', 'ignore'))
        except Exception:
            return []
    out = []
    for el in root.iter():
        if el.tag.split('}')[-1] not in ('item', 'entry'):
            continue
        rec = {}
        for ch in list(el):
            t = ch.tag.split('}')[-1]
            txt = ''.join(ch.itertext()).strip()
            if t == 'title' and not rec.get('title'):
                rec['title'] = txt
            elif t in ('description', 'summary', 'content', 'encoded') and not rec.get('desc'):
                rec['desc'] = txt
            elif t in ('pubDate', 'published', 'updated', 'date', 'dc:date') and not rec.get('time'):
                rec['time'] = txt
            elif t == 'link':
                href = ch.get('href') or txt
                if href and not rec.get('link'):
                    rec['link'] = href.strip()
        out.append(rec)
    return out


def _hot_norm(title, url, summary, source, label, color, kind, ts,
              points=0, comments=0, extra=None):
    title = (title or '').strip()
    url = (url or '').strip()
    if not title or not url.startswith('http'):
        return None
    summary = html_to_text(summary or '', 260)
    cat, cat_label, cat_color = hot_classify(title + ' ' + summary[:140])
    base = hashlib.md5((url.split('?')[0] + '|' + title.lower()).encode('utf-8')).hexdigest()[:12]
    return {
        'id': 'h' + base, 'title': title, 'titleZh': '', 'summary': summary,
        'url': url, 'source': source, 'sourceLabel': label, 'sourceColor': color,
        'category': cat, 'catLabel': cat_label, 'catColor': cat_color,
        'kind': kind, 'ts': ts, 'points': points, 'comments': comments,
        'heat': float(points + comments * 0.6 + (extra or 0)),
    }


def fetch_hot_rss(entry):
    key, label, url, color = entry
    raw = get(url, timeout=12)[0]
    rows = _rss_items(raw)
    out = []
    for r in rows[:18]:
        item = _hot_norm(r.get('title'), r.get('link'), r.get('desc'),
                         key, label, color, 'news', _hot_time(r.get('time')))
        if item:
            out.append(item)
    return out


def fetch_hot_hn(query=None):
    if query:
        u = 'https://hn.algolia.com/api/v1/search?' + urllib.parse.urlencode(
            {'query': query, 'tags': 'story', 'hitsPerPage': 10})
    else:
        u = 'https://hn.algolia.com/api/v1/search?tags=front_page&hitsPerPage=25'
    data = json.loads(get(u, timeout=10)[0])
    out = []
    for h in data.get('hits', []):
        item = _hot_norm(
            h.get('title') or h.get('story_title'),
            h.get('url') or ('https://news.ycombinator.com/item?id=%s' % h.get('objectID')),
            h.get('story_text'), 'hn', 'Hacker News', '#ff6600', 'community',
            _hot_time(h.get('created_at')), h.get('points') or 0,
            h.get('num_comments') or 0)
        if item:
            out.append(item)
    return out


def fetch_hot_github():
    since = (_dt.datetime.now(_dt.timezone.utc) - _dt.timedelta(days=45)).date().isoformat()
    u = ('https://api.github.com/search/repositories?' + urllib.parse.urlencode({
        'q': 'created:>%s' % since, 'sort': 'stars', 'order': 'desc', 'per_page': 12}))
    data = json.loads(get(u, timeout=12)[0])
    out = []
    for r in data.get('items', []):
        desc = r.get('description') or ''
        item = _hot_norm(
            r.get('full_name'), r.get('html_url'), desc,
            'github', 'GitHub Trending', '#24292f', 'project',
            _hot_time(r.get('created_at')), r.get('stargazers_count') or 0, 0,
            extra=(r.get('stargazers_count') or 0))
        if item:
            item['title'] = r.get('full_name') or item['title']
            item['summary'] = ('⭐ %s stars · %s' % (
                format(r.get('stargazers_count') or 0, ','), desc))[:260]
            out.append(item)
    return out


HOT_NOISE = re.compile(
    r'\b(black friday|cyber monday|prime day|deal|deals|sale|discount|coupon|'
    r'coupons|best (?:of|gift|deals?)|gift guide|xbox|playstation|nintendo|'
    r'bundle|streaming service|price drop|cheap|save \$|% off)\b', re.I)


def hot_rank(it, now):
    """Rank real-time + frontier relevance above consumer / promo filler."""
    age = max(0.0, now - (it['ts'] or 0))
    fresh = 6 if age < 86400 else (4 if age < 259200 else (2 if age < 604800 else 0))
    frontier = 3 if it['category'] != 'frontier' else 0
    heat = min(4.0, (it['heat'] or 0) / 60.0)
    noise = -6 if HOT_NOISE.search(it['title'] or '') else 0
    return fresh + frontier + heat + noise


HOT_TTL = 180
HOT_CACHE = {'ts': 0.0, 'items': [], 'sources': {}, 'failed': [], 'busy': False}
HOT_LOCK = threading.Lock()


def hot_refresh(force=False):
    """Rebuild the hotspot cache. Concurrent callers share one refresh."""
    with HOT_LOCK:
        if HOT_CACHE['busy']:
            return
        if not force and HOT_CACHE['items'] and (time.time() - HOT_CACHE['ts']) < HOT_TTL:
            return
        HOT_CACHE['busy'] = True
    jobs = []
    for e in HOT_RSS:
        jobs.append((e[0], lambda e=e: fetch_hot_rss(e)))
    jobs.append(('hn', lambda: fetch_hot_hn()))
    for topic in ('AI', 'semiconductor', 'quantum computing', 'space', 'biotech', 'robotics'):
        jobs.append(('hn:' + topic, lambda t=topic: fetch_hot_hn(t)))
    jobs.append(('github', fetch_hot_github))

    got, failed, counts = [], [], {}
    try:
        with ThreadPoolExecutor(max_workers=min(18, len(jobs))) as pool:
            futs = {pool.submit(fn): (name, fn) for name, fn in jobs}
            for f in as_completed(futs):
                name = futs[f][0]
                try:
                    rows = f.result() or []
                    if rows:
                        got.extend(rows)
                        counts[name.split(':')[0]] = counts.get(name.split(':')[0], 0) + len(rows)
                except Exception:
                    failed.append(name)

        # Dedupe by normalised title (cross-posting is common), keep the hottest.
        seen, uniq = {}, []
        for it in got:
            key = re.sub(r'[^a-z0-9\u4e00-\u9fff]+', '', it['title'].lower())[:56]
            if not key:
                key = it['url']
            if key in seen:
                old = seen[key]
                if it['heat'] > old['heat']:
                    uniq[uniq.index(old)] = it
                    seen[key] = it
                continue
            seen[key] = it
            uniq.append(it)
        for it in uniq:
            if not it['ts']:
                it['ts'] = time.time() - 3600  # undated feeds sink, never float to top
        # Recency + frontier relevance + community heat, minus consumer filler.
        _now = time.time()
        uniq.sort(key=lambda x: (hot_rank(x, _now), x['ts']), reverse=True)
        uniq = uniq[:120]
        # Gentle source diversity: avoid repeating a source within the last 3
        # rows, but always take the highest-ranked remaining item otherwise.
        # (A strict round-robin would ping-pong between the two largest feeds.)
        buckets = {}
        for it in uniq:
            buckets.setdefault(it['source'], []).append(it)
        ordered, recent = [], []
        while len(ordered) < len(uniq):
            candidates = [src for src in buckets
                          if buckets[src] and src not in recent[-3:]]
            if not candidates:
                candidates = [src for src in buckets if buckets[src]]
            if not candidates:
                break
            best = max(candidates, key=lambda s: hot_rank(buckets[s][0], _now))
            it = buckets[best].pop(0)
            ordered.append(it)
            recent.append(best)
        uniq = ordered
        with HOT_LOCK:
            HOT_CACHE['items'] = uniq
            HOT_CACHE['sources'] = counts
            HOT_CACHE['failed'] = failed
            HOT_CACHE['ts'] = time.time()
    finally:
        with HOT_LOCK:
            HOT_CACHE['busy'] = False

    # Progressive Chinese headlines: never block the JSON response, and the
    # translator has its own disk cache, so repeat polls are free.
    def _fill_zh():
        try:
            titles = [x['title'] for x in uniq[:40] if not x['titleZh']]
            zh = quickread.translate_many(titles, max_workers=2)
            if zh:
                with HOT_LOCK:
                    for x in HOT_CACHE['items']:
                        if not x['titleZh'] and x['title'] in zh:
                            x['titleZh'] = quickread.polish_translation(
                                zh[x['title']], x['title'])
        except Exception:
            pass
    threading.Thread(target=_fill_zh, name='hot-zh', daemon=True).start()


def do_hotspots(qs):
    force = qs.get('force') == '1'
    if force or not HOT_CACHE['items'] or (time.time() - HOT_CACHE['ts']) >= HOT_TTL:
        hot_refresh(force)
    with HOT_LOCK:
        items = [dict(x) for x in HOT_CACHE['items']]
        sources = dict(HOT_CACHE['sources'])
        failed = list(HOT_CACHE['failed'])
        updated = HOT_CACHE['ts']
        busy = HOT_CACHE['busy']
    cat = (qs.get('cat') or '').strip()
    if cat and cat != 'all':
        items = [x for x in items if x['category'] == cat]
    kind = (qs.get('kind') or '').strip()
    if kind:
        items = [x for x in items if x['kind'] == kind]
    try:
        since = float(qs.get('since') or 0)
    except ValueError:
        since = 0.0
    if since > 0:
        items = [x for x in items if x['ts'] > since]
    try:
        limit = max(1, min(120, int(qs.get('limit') or 60)))
    except ValueError:
        limit = 60
    cats = {}
    for x in HOT_CACHE['items']:
        cats[x['category']] = cats.get(x['category'], 0) + 1
    return {
        'ok': True, 'items': items[:limit], 'total': len(items),
        'updated': updated, 'nextRefresh': max(0, int(HOT_TTL - (time.time() - updated))),
        'sources': sources, 'failed': failed, 'cats': cats, 'busy': busy,
        'note': '前沿科技 · 实时新闻动态',
    }


def _hot_loop():
    """Keep the cache warm so the small-window push never waits on 16 feeds."""
    while True:
        time.sleep(HOT_TTL)
        try:
            hot_refresh(True)
        except Exception:
            pass


def track_search(topic):
    """Lightweight, TOPIC-RELEVANT search for the background tracker.

    Only academic indexes are queried (no news feeds, no platform cards):
    a tracking check should be fast, quiet and paper-only. arXiv's keyword
    query is an OR over individual words sorted by date, so without a second
    relevance pass a "gene editing" subscription would happily push today's
    newest image-editing / math preprints. We therefore require the paper's
    title (2 points) or abstract (1 point) to actually contain the topic's
    specific terms. Each source fails independently.
    """
    q_en = translate_query(topic)
    words = [w.lower() for w in
             re.findall(r"[A-Za-z][A-Za-z0-9\-]{2,}", q_en)]
    terms = [w for w in dict.fromkeys(words)
             if len(w) > 3 and w not in STOP and w not in quickread.STOP][:5]
    pats = [re.compile(r'\b' + re.escape(t) + r'\b', re.I) for t in terms]
    # A whole-phrase match ("artificial intelligence") is far stronger than a
    # lone generic word ("Artificial Currency" must NOT count as an AI paper).
    phrase = (re.compile(r'\b' + r'[\s\-]+'.join(re.escape(t) for t in terms)
                         + r'\b', re.I) if len(terms) > 1 else None)

    workers = (('arxiv', fetch_arxiv), ('openalex', fetch_openalex),
               ('crossref', fetch_crossref), ('pubmed', fetch_pubmed))
    out = []
    with ThreadPoolExecutor(max_workers=4) as pool:
        futs = {pool.submit(fn, q_en): name for name, fn in workers}
        for f in as_completed(futs):
            try:
                out.extend(f.result() or [])
            except Exception:
                continue
    if not pats or not out:
        return out

    def score(it):
        title, abstract = it.get('title') or '', it.get('abstract') or ''
        s = 4 if (phrase and phrase.search(title)) else (
            2 if (phrase and phrase.search(abstract)) else 0)
        hits = sum(1 for p in pats if p.search(title) or p.search(abstract))
        s += 3 if hits >= 2 else (1 if hits == 1 else 0)
        return s

    ranked = [(score(x), x) for x in out]
    strong = [x for s, x in ranked if s >= 3]
    if len(strong) < 4:                 # avoid an empty push on narrow topics
        weak = [x for s, x in ranked if 0 < s < 3]
        strong += weak[:4 - len(strong)]
    return strong


def build_jobs(raw_q):
    """Resolve the query and build the per-source job map (shared by the
    blocking /api/search and the streaming /api/search/stream endpoints)."""
    q_en = translate_query(raw_q)
    zh_q = zh_query_for(raw_q, q_en)

    # English/global sources use the translated query; the two new tabs get the
    # Chinese term / their own ranking strategy.
    jobs = {name: (lambda fn=fn: fn(q_en)) for name, fn in SOURCES.items()}
    jobs['cn'] = lambda: fetch_chinese(zh_q, raw_q, q_en)
    jobs['scholar'] = lambda: fetch_scholar_like(q_en, zh_q)
    return q_en, zh_q, jobs


def search_notes():
    # No developer-facing status text is shown in the product. Channel health
    # is handled silently by automatic fallbacks.
    return [], openalex_status()


def search_scholar_fallback(items, ok):
    """Scholar fallback: if that one call got rate-limited, re-rank real records
    the global OpenAlex source already returned. Nothing is fabricated — the
    same real papers are simply shown again under the Scholar-style view."""
    scholar_real = [x for x in items if x['source'] == 'scholar' and not x.get('entryLink')]
    if len(scholar_real) >= 3:
        return []
    pool = [x for x in items
            if (x.get('citedBy') or 0) > 0
            and x['source'] != 'scholar' and not x.get('entryLink')]
    pool.sort(key=lambda x: x['citedBy'], reverse=True)
    added = []
    for x in pool[:10]:
        y = dict(x)
        y['source'] = 'scholar'
        y['scholarUrl'] = scholar_link(x['title'])
        y['citedByLabel'] = '%s 次引用' % format(x['citedBy'], ',')
        items.append(y)
        added.append(y)
    if added:
        ok['scholar'] = ok.get('scholar', 0) + len(added)
    return added


# A repeated query (toggling filters, going back, two people searching the same
# term) must not re-run the whole fan-out. Results are cached briefly so the
# second view is instant while the index snapshot is still current.
SEARCH_CACHE = {}
SEARCH_CACHE_TTL = 180
SEARCH_CACHE_MAX = 48
SEARCH_LOCK = threading.Lock()


def _search_key(raw_q):
    return re.sub(r'\s+', ' ', (raw_q or '').strip().lower())


def _search_cache_get(raw_q):
    key = _search_key(raw_q)
    if not key:
        return None
    with SEARCH_LOCK:
        hit = SEARCH_CACHE.get(key)
        if hit and time.time() - hit[0] < SEARCH_CACHE_TTL:
            return hit[1]
    return None


def _search_cache_put(raw_q, payload):
    key = _search_key(raw_q)
    if not key:
        return
    with SEARCH_LOCK:
        if len(SEARCH_CACHE) >= SEARCH_CACHE_MAX:
            for k in sorted(SEARCH_CACHE, key=lambda k: SEARCH_CACHE[k][0])[:8]:
                SEARCH_CACHE.pop(k, None)
        SEARCH_CACHE[key] = (time.time(), payload)


def do_search(raw_q):
    cached = _search_cache_get(raw_q)
    if cached:
        return cached['result']

    q_en, zh_q, jobs = build_jobs(raw_q)

    ok, failed, items = {}, [], []
    with ThreadPoolExecutor(max_workers=9) as pool:
        futures = {pool.submit(fn): name for name, fn in jobs.items()}
        for f in as_completed(futures):
            name = futures[f]
            try:
                got = f.result() or []
                ok[name] = len(got)
                items.extend(got)
            except Exception as e:
                failed.append('%s: %s' % (name, type(e).__name__))
                ok[name] = 0

    search_scholar_fallback(items, ok)
    notes, oa_status = search_notes()
    result = {
        'items': items, 'sources': ok, 'failed': failed,
        'query': {'raw': raw_q, 'en': q_en, 'zh': zh_q},
        'notes': notes, 'openalexStatus': oa_status,
    }
    _search_cache_put(raw_q, {'result': result, 'batches': None})
    return result


def stream_search(raw_q):
    """Yield ('event', payload) as each source finishes.

    The panel renders every batch the moment it arrives, so fast sources show
    up immediately instead of the user waiting for the slowest one.
    """
    cached = _search_cache_get(raw_q)
    if cached and cached.get('batches'):
        # Replay the stored batches immediately: same frames, no wait.
        meta = cached['meta']
        yield ('meta', meta)
        for b in cached['batches']:
            yield ('batch', b)
        yield ('done', cached['done'])
        return

    q_en, zh_q, jobs = build_jobs(raw_q)
    total = len(jobs)
    done = 0
    ok, failed, items = {}, [], []
    batches = []
    meta = {'total': total, 'query': {'raw': raw_q, 'en': q_en, 'zh': zh_q}}
    yield ('meta', meta)

    with ThreadPoolExecutor(max_workers=9) as pool:
        futures = {pool.submit(fn): name for name, fn in jobs.items()}
        for f in as_completed(futures):
            name = futures[f]
            done += 1
            try:
                got = f.result() or []
                ok[name] = len(got)
                items.extend(got)
                frame = {'source': name, 'count': len(got),
                         'items': got, 'done': done, 'total': total,
                         'sources': dict(ok)}
                yield ('batch', frame)
                batches.append(frame)
            except Exception as e:
                failed.append('%s: %s' % (name, type(e).__name__))
                ok[name] = 0
                frame = {'source': name, 'count': 0, 'items': [],
                         'done': done, 'total': total,
                         'sources': dict(ok),
                         'error': type(e).__name__}
                yield ('batch', frame)
                batches.append(frame)

    extra = search_scholar_fallback(items, ok)
    if extra:
        frame = {'source': 'scholar', 'count': len(extra),
                 'items': extra, 'done': total, 'total': total,
                 'sources': dict(ok), 'extra': True}
        yield ('batch', frame)
        batches.append(frame)

    notes, oa_status = search_notes()
    final = {'sources': ok, 'failed': failed, 'notes': notes,
             'openalexStatus': oa_status,
             'query': {'raw': raw_q, 'en': q_en, 'zh': zh_q},
             'total': len(items)}
    _search_cache_put(raw_q, {'batches': batches, 'meta': meta,
                              'done': final,
                              'result': {'items': items, 'sources': ok,
                                         'failed': failed,
                                         'query': meta['query'],
                                         'notes': notes,
                                         'openalexStatus': oa_status}})
    yield ('done', final)


# ------------------------------------------------------------------- reading
def pubmed_full(pmid):
    url = 'https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?' + urllib.parse.urlencode(
        {'db': 'pubmed', 'id': pmid, 'retmode': 'xml'})
    root = ET.fromstring(get(url)[0])
    art = root.find('.//PubmedArticle')
    if art is None:
        return ''
    title = ''.join(art.find('.//ArticleTitle').itertext()) if art.find('.//ArticleTitle') is not None else ''
    abst = []
    for node in art.findall('.//Abstract/AbstractText'):
        lbl = node.get('Label') or ''
        txt = ''.join(node.itertext()).strip()
        abst.append((lbl + ': ' if lbl else '') + txt)
    journal = ''.join(art.find('.//Journal/Title').itertext()) if art.find('.//Journal/Title') is not None else ''
    authors = []
    for a in art.findall('.//AuthorList/Author'):
        ln = a.findtext('LastName') or ''
        fn = a.findtext('ForeName') or ''
        if ln:
            authors.append((fn + ' ' + ln).strip())
    parts = ['# ' + title, '', '**Journal:** ' + journal,
             '**Authors:** ' + ', '.join(authors[:12]), '', '## Abstract', '']
    parts += abst if abst else ['(No abstract available for this record.)']
    return '\n'.join(parts)


def do_read(p):
    source = p.get('source', '')
    url = p.get('url', '')
    pdf = p.get('pdf', '')
    pmid = p.get('pmid', '')
    pmcid = p.get('pmcid', '')
    title = p.get('title', '')
    text, note = '', ''

    # 1) PubMed: full abstract via official efetch
    if pmid:
        try:
            text = pubmed_full(pmid)
            note = 'PubMed 摘要 · 官方开放数据'
        except Exception as e:
            note = '摘要暂不可用'

    # 2) PMC: open-access HTML full text
    if not text and pmcid:
        try:
            raw, _ = get('https://www.ncbi.nlm.nih.gov/pmc/articles/%s/' % pmcid,
                         timeout=9)
            t = html_to_text(raw, 40000)
            if len(t) > 400:
                text = t
                note = 'PMC 开放获取全文'
        except Exception:
            pass

    # 3) arXiv: HTML full text when available, otherwise API abstract
    if not text and source == 'arxiv':
        aid = re.search(r'/abs/([0-9.]+v?\d*)', url)
        aid = aid.group(1) if aid else (p.get('arxivId') or '')
        if aid:
            try:
                raw, _ = get('https://arxiv.org/html/' + aid, timeout=6)
                t = html_to_text(raw, 40000)
                if len(t) > 600:
                    text = t
                    note = 'arXiv HTML 全文'
            except Exception:
                pass
            if not text:
                try:
                    q = 'https://export.arxiv.org/api/query?' + urllib.parse.urlencode({'id_list': aid})
                    root = ET.fromstring(get(q)[0])
                    e = root.find('a:entry', ATOM)
                    if e is not None:
                        s = e.find('a:summary', ATOM)
                        if s is not None:
                            text = '# ' + title + '\n\n## Abstract\n\n' + (s.text or '').strip()
                            note = 'arXiv 摘要'
                except Exception:
                    pass

    # 4) Generic: extract readable body text from the landing page
    if not text and url and not url.lower().endswith('.pdf'):
        try:
            raw, ct = fence(lambda: get(url, timeout=6), 7, None, True) or ('', '')
            if raw and 'pdf' not in ct.lower():
                t = html_to_text(raw, 25000)
                if len(t) > 200:
                    text = t
                    note = '网页全文'
        except Exception:
            pass

    # 5) Last resort: abstract already present in the search result
    if not text:
        text = p.get('abstract') or ''
        if text:
            note = '暂无开放全文，以下为文献摘要'

    return {'ok': True, 'text': text, 'pdf': pdf, 'note': note,
            'title': title, 'hasPdf': bool(pdf)}


# ------------------------------------------------- retired desktop integration
# The desktop file PDFMathReader-win32-x64.exe is an NSIS *portable wrapper*,
# not the Electron app itself: running it only unpacks/launches a program and
# it silently ignores a PDF path argument. It must never be reported as
# "已打开该 PDF". We look for the real installed exe first, and only fall back
# to the wrapper with honest feedback.
_PDFMR_CACHE = {'ts': 0, 'app': '', 'wrapper': ''}


def _is_nsis(path):
    try:
        with open(path, 'rb') as f:
            head = f.read(262144)
        return b'Nullsoft' in head or b'NSIS' in head
    except OSError:
        return False


def _mui_cache_exes():
    """Windows records GUI exes ever launched here; the portable build leaves
    the real (temp-extracted) Electron exe path behind in its value names."""
    out = []
    if os.name != 'nt':
        return out
    try:
        import winreg
        k = winreg.OpenKey(
            winreg.HKEY_CURRENT_USER,
            r'Software\Classes\Local Settings\Software\Microsoft\Windows\Shell\MuiCache')
        i = 0
        while True:
            try:
                name, _v, _t = winreg.EnumValue(k, i)
            except OSError:
                break
            i += 1
            if 'PDFMathReader.exe' in name:
                p = name.split('.exe', 1)[0] + '.exe'
                if os.path.isfile(p):
                    out.append(p)
        winreg.CloseKey(k)
    except Exception:
        pass
    return out


def locate_pdfmr(force=False):
    """Return {'app': real installed exe, 'wrapper': portable/installer exe}."""
    global _PDFMR_CACHE
    if not force and time.time() - _PDFMR_CACHE['ts'] < 30:
        return _PDFMR_CACHE
    home = os.path.expanduser('~')
    lad = os.environ.get('LOCALAPPDATA') or os.path.join(home, 'AppData', 'Local')
    rad = os.environ.get('APPDATA') or os.path.join(home, 'AppData', 'Roaming')
    tmp = os.environ.get('TEMP', '')
    dirs = [os.path.join(lad, 'Programs', 'PDFMathReader'),
            os.path.join(lad, 'Programs'), os.path.join(rad, 'PDFMathReader'),
            os.path.join(home, 'Desktop'), os.path.join(home, 'Downloads'),
            os.path.join(home, 'Documents'), ROOT,
            r'C:\Program Files', r'C:\Program Files (x86)', tmp]
    found = []
    env = os.environ.get('PDFMATHREADER_EXE', '').strip()
    if env:
        found.append(env)
    for d in dirs:
        try:
            found += glob.glob(os.path.join(d, 'PDFMathReader.exe'))
            found += glob.glob(os.path.join(d, '*', 'PDFMathReader.exe'))
            found += glob.glob(os.path.join(d, '*PDFMathReader*.exe'))
        except OSError:
            continue
    found += _mui_cache_exes()

    apps, wrappers = [], []
    for p in dict.fromkeys(found):
        if not os.path.isfile(p):
            continue
        (wrappers if _is_nsis(p) else apps).append(p)
    _PDFMR_CACHE = {'ts': time.time(),
                    'app': apps[0] if apps else '',
                    'wrapper': wrappers[0] if wrappers else ''}
    return _PDFMR_CACHE


def find_pdfmr_exe():
    """Backwards-compatible helper used by /api/health."""
    loc = locate_pdfmr()
    return loc['app'] or loc['wrapper'] or ''


def _spawn(args):
    try:
        subprocess.Popen(args, cwd=os.path.dirname(args[0]),
                         stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL,
                         close_fds=True)
        return True
    except Exception:
        return False


def _wait_for_extracted_app(before, seconds=7):
    """The NSIS portable wrapper unpacks the real Electron app into %TEMP%.
    Once it appears, a second instance forwards the PDF path to the running
    one through Electron's `second-instance` event."""
    tmp = os.environ.get('TEMP', '')
    if not tmp:
        return ''
    end = time.time() + seconds
    while time.time() < end:
        for p in glob.glob(os.path.join(tmp, '*', 'PDFMathReader.exe')):
            if p in before or not os.path.isfile(p) or _is_nsis(p):
                continue
            return p
        time.sleep(0.4)
    return ''


def do_launch(qs):
    """Download the PDF locally and hand it to the real desktop app.

    Never claim the PDF is open unless a real app exe received the path.
    """
    loc = locate_pdfmr(force=True)
    app, wrapper = loc['app'], loc['wrapper']
    if not app and not wrapper:
        return {'ok': False, 'mode': 'missing',
                'error': '未找到 PDFMathReader 程序本体（桌面上的是便携安装包）。'
                         '可先点「🚀 启动本地程序」，或设置环境变量 PDFMATHREADER_EXE 指向已安装的 PDFMathReader.exe'}

    url = qs.get('url', '')
    pdf_path = ''
    if url:
        if not re.match(r'^https?://', url):
            return {'ok': False, 'mode': 'missing', 'error': '非法的 PDF 链接'}
        try:
            raw = cached_pdf(url)
        except Exception as e:
            return {'ok': False, 'mode': 'missing',
                    'error': 'PDF 下载失败：%s' % type(e).__name__}
        if raw[:4] != b'%PDF':
            return {'ok': False, 'mode': 'missing',
                    'error': '该链接不是可直接下载的 PDF；请先用「🔎 查找免费 PDF」获取开放获取版本'}
        folder = os.path.join(ROOT, '_pdf')
        try:
            os.makedirs(folder, exist_ok=True)
            name = re.sub(r'[^0-9A-Za-z\u4e00-\u9fff_\-]+', '_',
                          qs.get('title') or 'paper')[:52] or 'paper'
            # content hash -> reopening the same paper never creates a duplicate
            pdf_path = os.path.join(folder, name + '_' +
                                    hashlib.md5(raw).hexdigest()[:8] + '.pdf')
            if not os.path.isfile(pdf_path):
                with open(pdf_path, 'wb') as f:
                    f.write(raw)
        except OSError as e:
            return {'ok': False, 'mode': 'missing', 'error': 'PDF 保存失败：%s' % e}

    result = {'ok': True, 'pdf': pdf_path,
              'pdfmathreader': app or wrapper, 'app': app, 'wrapper': wrapper}

    if app:
        started = _spawn([app] + ([pdf_path] if pdf_path else []))
        result.update(mode='opened' if started else 'failed',
                      message='已启动 PDFMathReader' +
                              ('并打开该 PDF' if pdf_path else ''))
        return result

    # Only a portable wrapper: start it, then try to reach the unpacked app.
    tmp = os.environ.get('TEMP', '')
    before = set(glob.glob(os.path.join(tmp, '*', 'PDFMathReader.exe'))) if tmp else set()
    _spawn([wrapper] + ([pdf_path] if pdf_path else []))
    extracted = _wait_for_extracted_app(before) if pdf_path else ''
    if extracted and pdf_path and _spawn([extracted, pdf_path]):
        result.update(mode='opened', app=extracted,
                      message='已启动 PDFMathReader 便携版并向程序传入该 PDF')
        locate_pdfmr(force=True)
        return result
    result.update(mode='launched',
                  message='已启动便携版 PDFMathReader；该便携包可能不接收文件参数，'
                          '若程序内未自动载入 PDF，请按 Ctrl+O 选择下方本地文件')
    return result


# ------------------------------------------------------------ home page cache
_HOME_CACHE = None
_HOME_LOCK = threading.Lock()


def _home_page():
    """Serve index.html with an mtime-based ETag; re-read only when it changes."""
    global _HOME_CACHE
    path = os.path.join(ROOT, 'index.html')
    st = os.stat(path)
    sig = (st.st_mtime_ns, st.st_size)
    with _HOME_LOCK:
        if _HOME_CACHE and _HOME_CACHE[0] == sig:
            return _HOME_CACHE[1], _HOME_CACHE[2]
        with open(path, 'rb') as f:
            raw = f.read()
        etag = '"%x-%x"' % sig
        _HOME_CACHE = (sig, raw, etag)
        return raw, etag


# ---------------------------------------------------------------------- HTTP
class Handler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'

    def log_message(self, fmt, *args):
        pass  # keep console quiet

    def handle_one_request(self):
        """Swallow client disconnects (the browser aborting a search when the
        user types a new keyword) instead of dumping a traceback."""
        try:
            BaseHTTPRequestHandler.handle_one_request(self)
        except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
            self.close_connection = True
        except socket.timeout:
            self.close_connection = True

    def _send(self, code, body, ctype, extra=None):
        if isinstance(body, str):
            body = body.encode('utf-8')
        # Text payloads (search JSON, reader HTML, page bundles) shrink 4-6x on
        # the wire, which is what makes the remote/public deployment feel fast
        # on a domestic uplink. Binary assets are never re-encoded.
        headers = dict(extra or {})
        enc = (self.headers.get('Accept-Encoding') or '').lower()
        compressible = (len(body) > 1400 and 'gzip' in enc and
                        ctype.split(';')[0].strip().lower().startswith(
                            ('text/', 'application/json',
                             'application/javascript',
                             'application/xml', 'image/svg')))
        if compressible:
            body = gzip.compress(body, 5)
            headers['Content-Encoding'] = 'gzip'
            headers.setdefault('Vary', 'Accept-Encoding')
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', headers.pop('Cache-Control', 'no-store'))
        # Allow the panel to talk to this service even when opened from the
        # preview host or directly via file://
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type')
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS')
        for k, v in headers.items():
            self.send_header(k, v)
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            self.close_connection = True

    def do_OPTIONS(self):
        self._send(204, b'', 'text/plain')

    def do_POST(self):
        """POST /api/enrich (quick-read metadata) or /api/track (subscriptions)."""
        path = urllib.parse.urlparse(self.path).path
        if path not in ('/api/enrich', '/api/track', '/api/net'):
            self._send(404, 'Not Found', 'text/plain; charset=utf-8')
            return
        try:
            size = int(self.headers.get('Content-Length', '0') or 0)
            if not 0 <= size <= 300000:
                raise ValueError('invalid body size')
            body = (json.loads(self.rfile.read(size).decode('utf-8', 'replace'))
                    if size else {})
            if path == '/api/net':
                if 'cnFirst' in body:
                    v = body['cnFirst']
                    with NET_LOCK:
                        NET['override'] = (None if v == 'auto' else bool(v))
                if body.get('recheck'):
                    probe_network(force=True)
                self._json(net_status())
                return
            if path == '/api/track':
                result, code = tracker.handle_post(body)
                self._json(result, code)
                return
            items = body.get('items') if isinstance(body, dict) else None
            if not isinstance(items, list):
                raise ValueError('items must be an array')
            result = quickread.enrich(items,
                                      mt=bool(body.get('mt')),
                                      full=bool(body.get('full')))
            self._json(result)
        except Exception as e:
            self._json({'ok': False, 'error': str(e), 'items': []}, 400)

    def _json(self, obj, code=200):
        self._send(code, json.dumps(_clean_display(obj), ensure_ascii=False),
                   'application/json; charset=utf-8')

    def _sse(self, raw_q):
        """Server-Sent Events: push each source's results as soon as it lands.

        Chunked transfer keeps the connection open, so the browser renders the
        first (fast) sources in a second or two instead of waiting for the
        slowest source to finish.
        """
        self.send_response(200)
        self.send_header('Content-Type', 'text/event-stream; charset=utf-8')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Accel-Buffering', 'no')
        self.send_header('Connection', 'close')
        self.send_header('Access-Control-Allow-Origin', '*')
        self.end_headers()
        try:
            for event, payload in stream_search(raw_q):
                chunk = ('event: %s\ndata: %s\n\n' % (
                    event, json.dumps(_clean_display(payload),
                                      ensure_ascii=False)))
                self.wfile.write(chunk.encode('utf-8'))
                self.wfile.flush()
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception:
            try:
                err = ('event: done\ndata: %s\n\n' % json.dumps(
                    {'failed': ['stream: %s' % type(e).__name__],
                     'sources': {}, 'notes': [], 'total': 0},
                    ensure_ascii=False))
                self.wfile.write(err.encode('utf-8'))
                self.wfile.flush()
            except Exception:
                pass
        finally:
            try:
                self.close_connection = True
            except Exception:
                pass

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        qs = {k: v[0] for k, v in urllib.parse.parse_qs(parsed.query).items()}

        if path == '/favicon.ico':
            self._send(204, b'', 'image/x-icon')
            return

        # PWA / brand assets. Exact whitelist only — never serve arbitrary files.
        static = {
            '/manifest.webmanifest': 'application/manifest+json; charset=utf-8',
            '/favicon.svg': 'image/svg+xml',
            '/icon-192.png': 'image/png',
            '/icon-512.png': 'image/png',
        }
        if path in static:
            try:
                with open(os.path.join(ROOT, path.lstrip('/')), 'rb') as f:
                    self._send(200, f.read(), static[path],
                               {'Cache-Control': 'public, max-age=86400, immutable'})
            except OSError:
                self._send(404, 'Not Found', 'text/plain; charset=utf-8')
            return

        if path in ('/', '/index.html'):
            try:
                raw, etag = _home_page()
                if self.headers.get('If-None-Match') == etag:
                    self._send(304, b'', 'text/html; charset=utf-8',
                               {'Cache-Control': 'no-cache'})
                    return
                self._send(200, raw, 'text/html; charset=utf-8',
                           {'Cache-Control': 'no-cache', 'ETag': etag})
            except OSError as e:
                self._send(404, str(e), 'text/plain; charset=utf-8')
            return

        if path == '/api/search':
            try:
                self._json(do_search(qs.get('q', '')))
            except Exception as e:
                self._json({'error': str(e), 'items': []}, 500)
            return

        if path == '/api/search/stream':
            self._sse(qs.get('q', ''))
            return

        if path == '/api/scholar':
            try:
                self._json(do_scholar_search(qs))
            except Exception as e:
                self._json({'ok': False, 'error': str(e), 'items': []}, 500)
            return

        if path == '/api/hotspots':
            try:
                self._json(do_hotspots(qs))
            except Exception as e:
                self._json({'ok': False, 'error': str(e), 'items': []}, 500)
            return

        if path == '/api/read':
            try:
                self._json(do_read(qs))
            except Exception as e:
                self._json({'ok': False, 'error': str(e), 'text': ''}, 500)
            return

        if path == '/api/pdf':
            target = qs.get('url', '')
            if not re.match(r'^https?://', target):
                self._send(400, 'invalid url', 'text/plain; charset=utf-8')
                return
            try:
                raw = cached_pdf(target, qs.get('doi', ''), qs.get('pmcid', ''),
                                 qs.get('title', ''))
                self._send(200, raw, 'application/pdf',
                           {'Content-Disposition': 'inline; filename="paper.pdf"'})
            except Exception:
                # Any publisher-side block / timeout becomes a calm branded
                # hand-off to the web full text. No technical error is shown.
                self._send(200, _PDF_FALLBACK_HTML, 'text/html; charset=utf-8',
                           {'Cache-Control': 'no-store'})
            return

        if path == '/api/asset':
            target = qs.get('url', '')
            if not re.match(r'^https?://', target):
                self._send(400, 'invalid url', 'text/plain; charset=utf-8')
                return
            try:
                raw, ctype = cached_asset(target)
                self._send(200, raw, ctype,
                           {'Cache-Control': 'public, max-age=600'})
            except Exception:
                # Graceful degradation: a failed asset must never render as a
                # broken-image icon or a raw error page inside the reader.
                low = target.lower()
                if low.endswith('.css') or 'stylesheet' in low:
                    body, ctype = b'/* stylesheet unavailable */', 'text/css; charset=utf-8'
                elif any(k in low for k in ('pixel', 'spacer', 'blank', '1x1',
                                            'tracking', 'logo', 'icon', 'avatar')):
                    body, ctype = BLANK_PNG, 'image/png'
                else:
                    body, ctype = PLACEHOLDER_SVG, 'image/svg+xml'
                self._send(200, body, ctype,
                           {'Cache-Control': 'public, max-age=120'})
            return

        if path == '/api/page':
            target = qs.get('url', '')
            if not re.match(r'^https?://', target):
                self._json({'ok': False, 'html': '', 'error': '非法链接'}, 400)
                return
            try:
                self._json(fetch_page(target))
            except Exception as e:
                self._json({'ok': False, 'html': '',
                            'error': '页面抓取失败：%s' % type(e).__name__}, 502)
            return

        if path == '/api/launch':
            # Retired endpoint. The desktop bundle is an NSIS portable
            # installer, not the app, and launching it used to produce a
            # misleading "already opened" message. Reading is fully in-panel.
            self._json({'ok': False, 'mode': 'removed',
                        'error': '该功能已下线，阅读统一在页面内完成'})
            return

        if path == '/api/reveal':
            p = os.path.abspath(qs.get('path', ''))
            folder = os.path.abspath(os.path.join(ROOT, '_pdf'))
            if not p.startswith(folder + os.sep) or not os.path.isfile(p):
                self._json({'ok': False, 'error': '文件不存在'}, 404)
                return
            try:
                subprocess.Popen(['explorer', '/select,' + p],
                                 stdin=subprocess.DEVNULL,
                                 stdout=subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL,
                                 close_fds=True)
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)}, 500)
            return

        if path == '/api/track':
            try:
                self._json(tracker.status())
            except Exception as e:
                self._json({'ok': False, 'error': str(e), 'inbox': []}, 500)
            return

        if path == '/api/net':
            # Cached probe; never blocks the UI for more than a few seconds.
            if not NET['checked']:
                probe_network()
            self._json(net_status())
            return

        if path == '/api/clean':
            # Legacy endpoint. Content filtering has been retired: return the
            # complete original page so no article content is ever stripped.
            target = qs.get('url', '')
            if not re.match(r'^https?://', target):
                self._json({'ok': False, 'html': '', 'error': '非法链接'}, 400)
                return
            try:
                self._json(fetch_page(target))
            except Exception:
                self._json({'ok': False, 'html': '', 'error': '页面暂不可用'}, 502)
            return

        if path == '/api/health':
            try:
                tr = tracker.status()
                track_brief = {'topics': tr['topics'], 'unread': tr['unread'],
                               'interval': tr['interval']}
            except Exception:
                track_brief = {'topics': [], 'unread': 0, 'interval': 0}
            # NOTE: do not probe the desktop PDFMathReader wrapper here. It is
            # an NSIS installer; touching it on every health poll used to
            # silently unpack/launch it. Reading is fully in-panel now.
            self._json({'ok': True, 'proxyConfigured': _HAS_PROXY,
                        'net': net_status(),
                        'track': track_brief, 'mt': quickread.mt_status()})
            return

        self._send(404, 'Not Found', 'text/plain; charset=utf-8')


# The tracker is wired here (after every source function exists) so importing
# server.py for tests does not silently start a background network thread.
tracker.init(track_search, quickread.enrich, quickread.glossary_title_zh)


if __name__ == '__main__':
    print('Xunzhe / Loreseek (loreseek.cn) listening on %s:%d' % (BIND_HOST, PORT))
    print('Proxy configured :  %s' % (urllib.request.getproxies() or 'none'))
    print('Subscription tracker: %s' % ', '.join(tracker.DEFAULT_TOPICS))
    print('Press Ctrl+C to stop.')
    srv = ThreadingHTTPServer((BIND_HOST, PORT), Handler)
    srv.daemon_threads = True
    # Network probe runs off the request path: a dead VPN proxy must not be
    # allowed to block search, and domestic sources must be ranked first.
    threading.Thread(target=probe_network, kwargs={'force': True},
                     name='net-probe', daemon=True).start()
    tracker.start_background()
    # Prime the independent hotspot cache off the request path, then keep it
    # warm so the small-window push always has fresh data ready instantly.
    threading.Thread(target=lambda: (hot_refresh(True), _hot_loop()),
                     name='hot-refresh', daemon=True).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print('\nStopped.')
