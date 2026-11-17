#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""寻哲 Loreseek (loreseek.cn) subscription tracker.

Turns the panel from "search when you remember" into an actual *tracking*
channel: the user subscribes to frontier-tech topics, a background thread
re-checks them periodically, and only genuinely new papers are pushed —
with freely readable open-access papers always first.

Design notes
  * The tracker never imports server.py (that would be circular). The search
    function and the quick-read enricher are injected via init().
  * State is persisted to .workbuddy-ai/track_state.json, so a restart does
    not re-push old papers.
  * A newly added topic first builds a *baseline*: historical hits are marked
    as seen, and only the newest few free papers are offered as a starting
    recommendation. Later checks push only real newcomers.
  * Only academic papers are tracked. News / platform entry cards are dropped,
    and papers with no plausible free route are not pushed at all.

Standard library only.
"""
import json
import os
import re
import time
import hashlib
import threading
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.abspath(__file__))
STATE_PATH = os.path.join(ROOT, '.workbuddy-ai', 'track_state.json')

DEFAULT_TOPICS = ['人工智能', '量子计算', '基因编辑']
INTERVAL = int(os.environ.get('LORESEEK_TRACK_INTERVAL', '1200'))  # 20 min
INBOX_MAX = 60
SEEN_MAX = 400
START_PUSH = 4          # free papers offered when a topic is first subscribed

_LOCK = threading.RLock()
_STATE = None
_SEARCH = None          # injected: topic -> list of raw items
_ENRICH = None          # injected: quickread.enrich
_GLOSSARY = None        # injected: quickread.glossary_title_zh
_STARTED = False
_CHECKING = False
_LAST_ERROR = ''

CJK = re.compile(r'[\u4e00-\u9fff]')


def init(search_fn, enrich_fn, glossary_fn=None):
    global _SEARCH, _ENRICH, _GLOSSARY
    _SEARCH, _ENRICH, _GLOSSARY = search_fn, enrich_fn, glossary_fn


# ------------------------------------------------------------------ state
def _blank():
    return {'topics': list(DEFAULT_TOPICS), 'seen': {}, 'inbox': [],
            'lastCheck': 0, 'checks': 0, 'baselineDone': {}}


def _load():
    global _STATE
    if _STATE is not None:
        return _STATE
    try:
        with open(STATE_PATH, 'r', encoding='utf-8') as f:
            d = json.load(f)
        if isinstance(d, dict) and isinstance(d.get('topics'), list):
            d.setdefault('seen', {})
            d.setdefault('inbox', [])
            d.setdefault('lastCheck', 0)
            d.setdefault('checks', 0)
            d.setdefault('baselineDone', {})
            _STATE = d
            return _STATE
    except (OSError, ValueError):
        pass
    _STATE = _blank()
    return _STATE


def _save():
    """Atomic write: a crash mid-write must not corrupt the seen-set."""
    try:
        os.makedirs(os.path.dirname(STATE_PATH), exist_ok=True)
        tmp = STATE_PATH + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(_STATE, f, ensure_ascii=False)
        os.replace(tmp, STATE_PATH)
    except OSError:
        pass


def _stable_id(it):
    for k in ('doi', 'pdfUrl', 'url'):
        v = (it.get(k) or '').strip().lower()
        if v and not v.startswith('#'):
            return v
    t = re.sub(r'\W+', '', (it.get('title') or '').lower())
    return 'title:' + hashlib.md5(t.encode('utf-8', 'ignore')).hexdigest()[:16]


def _is_pushable(it, enrich):
    """Push papers with a free route; never push news or search-entry cards."""
    if it.get('entryLink') or it.get('isPlatformCard'):
        return False
    src = (it.get('source') or '').lower()
    if src in ('hn', 'techcrunch', 'nature'):
        return False
    return (enrich.get('freeScore', 2) if isinstance(enrich, dict) else 2) <= 1


def _slim(it):
    """Only the fields the panel needs — keeps the state file small."""
    keys = ('title', 'abstract', 'url', 'pdfUrl', 'freePreviewUrl', 'date',
            'authors', 'journal', 'doi', 'pmid', 'pmcid', 'arxivId',
            'isOA', 'citedBy', 'source', 'scholarUrl', 'oaStatus')
    out = {k: it[k] for k in keys if it.get(k) not in (None, '', [])}
    out['source'] = it.get('source', '')
    return out


def _decorate(items):
    """Attach bilingual quick-read metadata without touching the network."""
    if not items:
        return []
    if _ENRICH is None:
        return items
    payload = [{'id': _stable_id(x), 'title': x.get('title', ''),
                'abstract': x.get('abstract', ''), 'source': x.get('source', ''),
                'isOA': x.get('isOA'), 'pdfUrl': x.get('pdfUrl'),
                'freePreviewUrl': x.get('freePreviewUrl'),
                'pmcid': x.get('pmcid'), 'doi': x.get('doi')}
               for x in items]
    try:
        enriched = _ENRICH(payload, mt=False)['items']
    except Exception:
        return items
    out = []
    for raw, e in zip(items, enriched):
        d = dict(raw)
        # mt=False keeps untranslated candidates for a later MT pass, but the
        # inbox never runs that pass. Ship only Chinese-glossed keywords so the
        # "every paper has bilingual keywords" promise also holds for pushes.
        raw_kws = e.get('keywords', [])
        kws = [k for k in raw_kws if k.get('zh')]
        d['keywords'] = kws or [{'en': 'frontier tech', 'zh': '前沿科技',
                                 'via': 'generic'}]
        d['titleZh'] = e.get('titleZh', '')
        d['titleZhVia'] = e.get('titleZhVia', '')
        # Show something useful immediately: an honest Chinese keyword line,
        # not a "中文标题生成中…" placeholder. The panel upgrades it to a real
        # machine-translated headline asynchronously when the drawer opens.
        if not d['titleZh']:
            if CJK.search(raw.get('title') or ''):
                d['titleZh'], d['titleZhVia'] = raw['title'], 'native'
            elif _GLOSSARY:
                fb = _GLOSSARY(raw.get('title', ''), raw_kws)
                if fb:
                    d['titleZh'], d['titleZhVia'] = fb, 'glossary'
        d['freeScore'] = e.get('freeScore', 2)
        d['freeLabel'] = e.get('freeLabel', '')
        d['kind'] = e.get('kind', 'paper')
        out.append(d)
    return out


# ------------------------------------------------------------------ checking
def _check_topic(topic, st):
    """Return (new_items, all_ids, error)."""
    if _SEARCH is None:
        return [], [], 'tracker not initialised'
    try:
        raw = _SEARCH(topic) or []
    except Exception as e:
        return [], [], type(e).__name__

    # dedupe inside one search result
    uniq, seen_here = [], set()
    for it in raw:
        if not (it.get('title') or '').strip():
            continue
        sid = _stable_id(it)
        if sid in seen_here:
            continue
        seen_here.add(sid)
        uniq.append(it)
    if not uniq:
        return [], [], ''

    decorated = _decorate([_slim(x) for x in uniq])
    candidates = [d for d in decorated if _is_pushable(d, d)]
    # Stable two-pass sort: free full text first, newest first within a level.
    candidates.sort(key=lambda d: d.get('date') or '', reverse=True)
    candidates.sort(key=lambda d: d.get('freeScore', 2))
    free = [d for d in candidates if d.get('freeScore') == 0]

    known = set(st['seen'].get(topic, []))
    baseline = not st['baselineDone'].get(topic) and not known
    fresh = [d for d in candidates if _stable_id(d) not in known]
    all_ids = list(dict.fromkeys([_stable_id(d) for d in candidates] + list(known)))

    now = time.time()
    if baseline:
        # First subscription: do not dump a hundred historical papers on the
        # user. Offer a handful of the newest FREE full-text papers instead.
        picked = free[:START_PUSH]
        for i, d in enumerate(picked):
            d['_topic'] = topic
            # Slightly larger for higher-ranked items: -_at sorting then keeps
            # the newest paper FIRST instead of reversing a same-batch push.
            d['_at'] = now + (len(picked) - i) * 0.001
            d['_id'] = _stable_id(d)
            d['_read'] = False
            d['_initial'] = True
        return picked, all_ids[:SEEN_MAX], ''

    picked = []
    for i, d in enumerate(fresh):
        d['_topic'] = topic
        d['_at'] = now + (len(fresh) - i) * 0.001
        d['_id'] = _stable_id(d)
        d['_read'] = False
        picked.append(d)
    # Free full text is pushed ahead of "a free copy may exist".
    picked.sort(key=lambda d: (d.get('freeScore', 2), -d.get('_at', 0)))
    # Never flood: cap a single topic's push per check.
    return picked[:12], all_ids[:SEEN_MAX], ''


def check_all(force=False):
    """Check every subscribed topic. Returns a short summary dict."""
    global _CHECKING, _LAST_ERROR
    with _LOCK:
        if _CHECKING:
            return {'ok': True, 'checking': True, 'added': 0,
                    'note': '正在检查中'}
        st = _load()
        if not force and st.get('lastCheck') and \
                time.time() - st['lastCheck'] < INTERVAL:
            return {'ok': True, 'added': 0, 'skipped': True,
                    'note': '未到下次检查时间'}
        _CHECKING = True
        topics = list(st['topics'])
    added, errors = 0, []
    try:
        for topic in topics:
            picked, ids, err = _check_topic(topic, _load())
            if err:
                errors.append('%s: %s' % (topic, err))
            with _LOCK:
                st = _load()
                if ids:
                    st['seen'][topic] = ids
                st['baselineDone'][topic] = True
                for d in picked:
                    if any(x.get('_id') == d['_id'] for x in st['inbox']):
                        continue
                    st['inbox'].append(d)
                    added += 1
                # free first, then newest
                st['inbox'].sort(key=lambda x: (x.get('freeScore', 2),
                                                -x.get('_at', 0)))
                st['inbox'] = st['inbox'][:INBOX_MAX]
                st['lastCheck'] = time.time()
                st['checks'] = st.get('checks', 0) + 1
                _save()
    finally:
        with _LOCK:
            _CHECKING = False
            _LAST_ERROR = '; '.join(errors[:3])
    return {'ok': True, 'added': added, 'errors': errors,
            'note': _LAST_ERROR or '检查完成'}


def start_background():
    """Daemon thread: no extra process, no scheduler, no OS hooks."""
    global _STARTED
    if _STARTED:
        return
    _STARTED = True

    def loop():
        # Give the server a moment to settle before the first network check.
        time.sleep(20)
        while True:
            try:
                check_all()
            except Exception:
                pass
            time.sleep(30)

    threading.Thread(target=loop, name='loreseek-tracker', daemon=True).start()


def request_check():
    """User pressed 'check now': run it off the HTTP request thread."""
    def run():
        check_all(force=True)
    threading.Thread(target=run, name='loreseek-track-check',
                     daemon=True).start()


# ------------------------------------------------------------------ API
def status():
    with _LOCK:
        st = _load()
        inbox = _decorate([{k: v for k, v in x.items()
                            if not k.startswith('_')} for x in st['inbox']])
        # carry tracker-only flags back onto the decorated copies
        for src, dst in zip(st['inbox'], inbox):
            for k in ('_topic', '_at', '_id', '_read', '_initial'):
                dst[k] = src.get(k)
        unread = sum(1 for x in inbox if not x.get('_read'))
        free = sum(1 for x in inbox if x.get('freeScore') == 0 and not x.get('_read'))
        last = st.get('lastCheck') or 0
        return {
            'ok': True, 'topics': list(st['topics']), 'inbox': inbox,
            'unread': unread, 'freeUnread': free,
            'lastCheck': last, 'checks': st.get('checks', 0),
            'interval': INTERVAL, 'checking': _CHECKING,
            'nextCheck': (last + INTERVAL) if last else 0,
            'error': _LAST_ERROR,
            'note': '仅推送免费全文 / 可查免费版的论文；每 %d 分钟自动检查一次' % (INTERVAL // 60),
        }


def set_topics(topics):
    """Replace the subscription list; return the added topics."""
    clean = []
    for t in topics or []:
        t = (t or '').strip()[:40]
        if t and t not in clean:
            clean.append(t)
    clean = clean[:8]
    with _LOCK:
        st = _load()
        old = set(st['topics'])
        st['topics'] = clean
        for t in clean:
            st['seen'].setdefault(t, [])
        for t in list(st['seen']):
            if t not in clean:
                st['seen'].pop(t, None)
                st['baselineDone'].pop(t, None)
        st['inbox'] = [x for x in st['inbox'] if x.get('_topic') in clean]
        added = [t for t in clean if t not in old]
        _save()
    if added:
        # Build the baseline for the new topics without blocking the UI.
        def run():
            for t in added:
                with _LOCK:
                    s = _load()
                    s['baselineDone'][t] = False
                try:
                    picked, ids, _ = _check_topic(t, _load())
                except Exception:
                    continue
                with _LOCK:
                    s = _load()
                    s['seen'][t] = ids
                    s['baselineDone'][t] = True
                    for d in picked:
                        if not any(x.get('_id') == d['_id'] for x in s['inbox']):
                            s['inbox'].append(d)
                    s['inbox'].sort(key=lambda x: (x.get('freeScore', 2),
                                                    -x.get('_at', 0)))
                    s['inbox'] = s['inbox'][:INBOX_MAX]
                    _save()
        threading.Thread(target=run, name='loreseek-track-baseline',
                         daemon=True).start()
    return {'ok': True, 'topics': clean, 'added': added}


def mark_read():
    with _LOCK:
        st = _load()
        for x in st['inbox']:
            x['_read'] = True
        _save()
    return {'ok': True, 'unread': 0}


def clear_inbox():
    with _LOCK:
        st = _load()
        st['inbox'] = []
        _save()
    return {'ok': True}


def handle_post(body):
    if not isinstance(body, dict):
        return {'ok': False, 'error': 'body must be an object'}, 400
    if 'topics' in body:
        return set_topics(body.get('topics')), 200
    action = (body.get('action') or '').lower()
    if action == 'check':
        request_check()
        return {'ok': True, 'checking': True, 'note': '已开始后台检查，约 10–30 秒后刷新'}, 200
    if action == 'read':
        return mark_read(), 200
    if action == 'clear':
        return clear_inbox(), 200
    return {'ok': False, 'error': 'unknown action'}, 400
