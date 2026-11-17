# -*- coding: utf-8 -*-
"""寻哲 Loreseek (loreseek.cn) "quick read" intelligence.

Turns a raw search hit into something that can be judged in ~3 seconds:

* keywords  - 5 domain terms extracted from title + abstract, each with a
              Chinese gloss (local bilingual dictionaries, no network needed)
* titleZh   - Chinese title, from a batched MT call with a persistent cache;
              when the free quota is gone it degrades to an honest glossary
              label instead of pretending to be a literal translation
* summaryZh - 1-2 Chinese "takeaway" lines for the immersive reader
* freeLevel - how certainly the paper can be read for free (free/partial/
              unknown); the feed sorts free papers to the front by default

All network work is optional and asynchronous from the browser's point of
view: callers first request ``mt=False`` for instant local fields, then
``mt=True`` in small visible batches to fill in the translations.
"""

import hashlib
import json
import os
import re
import threading
import time
import urllib.parse
import urllib.request
import urllib.error
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = os.path.dirname(os.path.abspath(__file__))
CACHE_PATH = os.path.join(ROOT, '.workbuddy-ai', 'quickread_cache.json')
UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) Loreseek/1.0 (xunzhe; local research client)'

CJK = re.compile(r'[\u4e00-\u9fff]')
TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9\-']*")
CN_TOKEN_RE = re.compile(r'[\u4e00-\u9fff]{2,8}')

# ----------------------------------------------------------- bilingual terms
# Injected by server.py so the existing search dictionary is reused rather
# than duplicated. Keys are lowercase English phrases, values Chinese.
TERM_ZH = {}

# Extra phrase-level glossary: common frontier-tech academic expressions.
TERM_EXTRA = [
    ('注意力机制', 'attention mechanism'), ('自注意力', 'self-attention'),
    ('微调', 'fine-tuning'), ('预训练', 'pre-training'), ('预训练模型', 'pretrained model'),
    ('零样本', 'zero-shot'), ('少样本', 'few-shot'), ('思维链', 'chain of thought'),
    ('模型对齐', 'alignment'), ('人类反馈', 'human feedback'), ('幻觉', 'hallucination'),
    ('提示词', 'prompt'), ('词元', 'token'), ('上下文窗口', 'context window'),
    ('模型蒸馏', 'knowledge distillation'), ('模型压缩', 'model compression'),
    ('推理加速', 'inference acceleration'), ('量化', 'quantization'),
    ('参数高效微调', 'parameter efficient fine-tuning'),
    ('多智能体', 'multi-agent'), ('智能体', 'agent'), ('工具调用', 'tool use'),
    ('向量数据库', 'vector database'), ('语义检索', 'semantic search'),
    ('基准测试', 'benchmark'), ('消融实验', 'ablation'), ('泛化能力', 'generalization'),
    ('可解释性', 'interpretability'), ('鲁棒性', 'robustness'), ('公平性', 'fairness'),
    ('隐私保护', 'privacy preservation'), ('差分隐私', 'differential privacy'),
    ('对抗攻击', 'adversarial attack'), ('越狱攻击', 'jailbreak'),
    ('图像生成', 'image generation'), ('视频生成', 'video generation'),
    ('目标检测', 'object detection'), ('语义分割', 'semantic segmentation'),
    ('三维重建', '3d reconstruction'), ('点云', 'point cloud'),
    ('具身智能', 'embodied intelligence'), ('强化学习', 'reinforcement learning'),
    ('世界模型', 'world model'), ('仿真环境', 'simulation environment'),
    ('量子比特', 'qubit'), ('量子门', 'quantum gate'), ('表面码', 'surface code'),
    ('量子优越性', 'quantum advantage'), ('量子纠错', 'quantum error correction'),
    ('退相干', 'decoherence'), ('超导电路', 'superconducting circuit'),
    ('光量子', 'photonic quantum'), ('量子模拟', 'quantum simulation'),
    ('钙钛矿太阳能电池', 'perovskite solar cell'), ('光电转换效率', 'power conversion efficiency'),
    ('固态电解质', 'solid electrolyte'), ('锂枝晶', 'lithium dendrite'),
    ('电催化', 'electrocatalysis'), ('析氢反应', 'hydrogen evolution reaction'),
    ('二维材料', 'two-dimensional material'), ('异质结', 'heterostructure'),
    ('超导', 'superconductivity'), ('拓扑绝缘体', 'topological insulator'),
    ('分子动力学', 'molecular dynamics'), ('第一性原理', 'first principles'),
    ('基因编辑', 'gene editing'), ('基因治疗', 'gene therapy'),
    ('单细胞测序', 'single-cell sequencing'), ('空间转录组', 'spatial transcriptomics'),
    ('蛋白质折叠', 'protein folding'), ('结构预测', 'structure prediction'),
    ('临床试验', 'clinical trial'), ('队列研究', 'cohort study'),
    ('生物标志物', 'biomarker'), ('免疫应答', 'immune response'),
    ('药物筛选', 'drug screening'), ('递送系统', 'delivery system'),
    ('信使核糖核酸', 'mRNA'),
    ('可控核聚变', 'nuclear fusion'), ('托卡马克', 'tokamak'),
    ('等离子体', 'plasma'), ('碳捕集', 'carbon capture'),
    ('储能系统', 'energy storage'), ('电网', 'power grid'),
    ('遥感', 'remote sensing'), ('卫星星座', 'satellite constellation'),
    ('深空探测', 'deep space exploration'), ('引力波', 'gravitational wave'),
    ('暗物质', 'dark matter'), ('系外行星', 'exoplanet'),
    ('大语言模型', 'large language model'), ('扩散模型', 'diffusion model'),
    ('图神经网络', 'graph neural network'), ('Transformer', 'transformer'),
    ('检索增强生成', 'retrieval augmented generation'),
    ('联邦学习', 'federated learning'), ('对比学习', 'contrastive learning'),
    ('神经网络', 'neural network'), ('深度学习', 'deep learning'),
    ('机器学习', 'machine learning'), ('计算机视觉', 'computer vision'),
    ('自然语言处理', 'natural language processing'),
    ('生成式人工智能', 'generative ai'), ('通用人工智能', 'artificial general intelligence'),
    ('脑机接口', 'brain computer interface'), ('自动驾驶', 'autonomous driving'),
    ('边缘计算', 'edge computing'), ('网络安全', 'cybersecurity'),
    ('区块链', 'blockchain'), ('开源模型', 'open source model'),
    ('数据集', 'dataset'), ('开源', 'open source'), ('综述', 'survey'),
]

# Word-level glossary used to gloss keywords that miss the phrase dictionary.
WORD_ZH = {
    'attention': '注意力', 'transformer': 'Transformer', 'model': '模型',
    'models': '模型', 'language': '语言', 'large': '大规模', 'learning': '学习',
    'deep': '深度', 'neural': '神经', 'network': '网络', 'networks': '网络',
    'training': '训练', 'inference': '推理', 'reasoning': '推理',
    'generation': '生成', 'generative': '生成式', 'retrieval': '检索',
    'augmented': '增强', 'alignment': '对齐', 'agent': '智能体', 'agents': '智能体',
    'benchmark': '基准测试', 'evaluation': '评估', 'dataset': '数据集',
    'framework': '框架', 'method': '方法', 'methods': '方法', 'approach': '方法',
    'architecture': '架构', 'system': '系统', 'systems': '系统',
    'performance': '性能', 'efficiency': '效率', 'accuracy': '准确率',
    'robustness': '鲁棒性', 'generalization': '泛化', 'scalability': '可扩展性',
    'optimization': '优化', 'algorithm': '算法', 'algorithms': '算法',
    'quantum': '量子', 'qubit': '量子比特', 'qubits': '量子比特',
    'error': '误差', 'correction': '纠正', 'code': '编码', 'codes': '编码',
    'entanglement': '纠缠', 'simulation': '模拟', 'computing': '计算',
    'photonic': '光子', 'superconducting': '超导', 'threshold': '阈值',
    'protein': '蛋白质', 'structure': '结构', 'prediction': '预测',
    'gene': '基因', 'genome': '基因组', 'genomic': '基因组', 'cell': '细胞',
    'cells': '细胞', 'clinical': '临床', 'trial': '试验', 'cancer': '肿瘤',
    'tumor': '肿瘤', 'immune': '免疫', 'therapy': '治疗', 'drug': '药物',
    'discovery': '发现', 'delivery': '递送', 'vaccine': '疫苗',
    'solar': '太阳能', 'battery': '电池', 'batteries': '电池',
    'electrolyte': '电解质', 'catalyst': '催化剂', 'catalysis': '催化',
    'material': '材料', 'materials': '材料', 'crystal': '晶体',
    'semiconductor': '半导体', 'chip': '芯片', 'chips': '芯片',
    'fusion': '聚变', 'plasma': '等离子体', 'energy': '能源',
    'renewable': '可再生', 'storage': '储能', 'carbon': '碳',
    'emission': '排放', 'climate': '气候', 'grid': '电网',
    'satellite': '卫星', 'rocket': '火箭', 'spacecraft': '航天器',
    'telescope': '望远镜', 'exoplanet': '系外行星', 'galaxy': '星系',
    'robot': '机器人', 'robotics': '机器人学', 'autonomous': '自主',
    'driving': '驾驶', 'control': '控制', 'perception': '感知',
    'security': '安全', 'privacy': '隐私', 'attack': '攻击', 'detection': '检测',
    'segmentation': '分割', 'image': '图像', 'images': '图像',
    'video': '视频', 'vision': '视觉', 'multimodal': '多模态',
    'graph': '图', 'diffusion': '扩散', 'federated': '联邦',
    'distributed': '分布式', 'cloud': '云', 'edge': '边缘',
    'database': '数据库', 'compiler': '编译器', 'scheduling': '调度',
    'survey': '综述', 'review': '综述', 'study': '研究', 'analysis': '分析',
    'design': '设计', 'novel': '新型', 'new': '新型', 'efficient': '高效',
    'efficiently': '高效', 'towards': '面向', 'toward': '面向',
    'via': '基于', 'using': '使用', 'based': '基于', 'for': '用于',
    'with': '与', 'and': '与', 'of': '的', 'in': '在', 'on': '关于',
    'data': '数据', 'knowledge': '知识', 'task': '任务', 'tasks': '任务',
    'human': '人类', 'feedback': '反馈', 'reward': '奖励', 'policy': '策略',
    'state': '状态', 'space': '空间', 'representation': '表示',
    'embedding': '嵌入', 'embeddings': '嵌入', 'token': '词元',
    'prompt': '提示词', 'prompting': '提示', 'context': '上下文',
    'open': '开放', 'source': '源码', 'benchmarking': '基准评测',
    # Wider academic / industry vocabulary. These are deliberately generic:
    # they let news-style headlines still produce meaningful Chinese keywords
    # when the online translation quota is exhausted.
    'foundation': '基础', 'adaptation': '适配', 'adapt': '适配',
    'specific': '特定', 'contrastive': '对比', 'explanation': '解释',
    'explanations': '解释', 'measurement': '测量', 'measuring': '测量',
    'comparative': '比较', 'comparison': '比较', 'stability': '稳定性',
    'frequency': '频率', 'invariance': '不变性', 'series': '序列',
    'sensor': '传感器', 'sensors': '传感器', 'sensing': '感知',
    'signal': '信号', 'signals': '信号', 'planner': '规划器',
    'planning': '规划', 'workflow': '工作流', 'workflows': '工作流',
    'tool': '工具', 'tools': '工具', 'questioning': '提问',
    'ideation': '构思', 'player': '参与者', 'unified': '统一',
    'geometry': '几何', 'geometric': '几何', 'household': '家庭',
    'behavior': '行为', 'challenge': '挑战', 'challenges': '挑战',
    'solution': '方案', 'solutions': '方案', 'resource': '资源',
    'constrained': '受限', 'project': '项目', 'surplus': '剩余',
    'consumer': '消费者', 'currency': '货币', 'selling': '销售',
    'approximation': '近似', 'assessment': '评估', 'infrastructure': '基础设施',
    'revenue': '营收', 'quarterly': '季度', 'contract': '合同',
    'contracts': '合同', 'board': '董事会', 'global': '全球',
    'emerging': '新兴', 'manager': '管理人', 'environment': '环境',
    'environmental': '环境', 'wildlife': '野生动物', 'drought': '干旱',
    'droughts': '干旱', 'extinction': '灭绝', 'extreme': '极端',
    'sample': '采样', 'sampling': '采样', 'distilling': '蒸馏',
    'dissecting': '剖析', 'competing': '竞争性', 'versus': '对比',
    'community': '社群', 'communities': '社群', 'bound': '界限',
    'accuracy': '准确率', 'efficiency': '效率', 'scalable': '可扩展',
    'deployment': '部署', 'production': '生产', 'industry': '产业',
    'company': '公司', 'companies': '公司', 'market': '市场',
    'startup': '初创公司', 'funding': '融资', 'investment': '投资',
    'policy': '策略', 'policies': '策略', 'regulation': '监管',
    'chipmaker': '芯片厂商', 'gpu': 'GPU', 'compute': '算力',
    'datacenter': '数据中心', 'cloud': '云', 'release': '发布',
    'launch': '发布', 'feature': '功能', 'features': '功能',
    'update': '更新', 'platform': '平台', 'product': '产品',
    'safety': '安全', 'risk': '风险', 'risks': '风险',
    'science': '科学', 'scientist': '科学家', 'scientists': '科学家',
    'researcher': '研究者', 'researchers': '研究者', 'evidence': '证据',
    'experiment': '实验', 'experiments': '实验', 'observation': '观测',
    'frontier': '前沿', 'tech': '科技', 'news': '资讯',
}

STOP = {
    'a', 'an', 'the', 'and', 'or', 'but', 'if', 'of', 'in', 'on', 'at', 'to',
    'for', 'from', 'with', 'by', 'as', 'is', 'are', 'was', 'were', 'be', 'been',
    'being', 'this', 'that', 'these', 'those', 'it', 'its', 'we', 'our', 'us',
    'they', 'their', 'you', 'your', 'i', 'not', 'no', 'can', 'may', 'more',
    'most', 'than', 'into', 'over', 'under', 'between', 'through', 'during',
    'via', 'using', 'use', 'used', 'based', 'approach', 'study', 'studies',
    'paper', 'work', 'works', 'result', 'results', 'show', 'shows', 'shown',
    'propose', 'proposed', 'present', 'presents', 'introduce', 'introduces',
    'new', 'novel', 'first', 'second', 'also', 'however', 'while', 'which',
    'such', 'here', 'both', 'each', 'other', 'some', 'all', 'any', 'one',
    'two', 'three', 'towards', 'toward', 'large', 'small', 'high', 'low',
    'research', 'science', 'scientific', 'analysis', 'review', 'letter',
    'http', 'https', 'doi', 'arxiv', 'etal', 'preprint', 'vol', 'pp',
}

NEWS_SOURCES = {'hn', 'techcrunch'}
FREE_SOURCES = {'arxiv', 'pwc', 'cn'}


def register_terms(cn_map, abbr=None):
    """Reuse server.py's CN/EN dictionary as the phrase glossary."""
    for zh, en in (cn_map or []):
        # keep the FIRST (most precise) Chinese term for duplicate English
        TERM_ZH.setdefault((en or '').lower().strip(), zh)
    for zh, en in TERM_EXTRA:
        TERM_ZH.setdefault(en.lower().strip(), zh)
    rev = {en: zh for zh, en in (cn_map or [])}
    for short, full in (abbr or {}).items():
        zh = rev.get(full.lower())
        if zh:
            TERM_ZH.setdefault(short.lower(), zh)
    return len(TERM_ZH)


# ------------------------------------------------------------ keyword mining
def _clean(text):
    return re.sub(r'\s+', ' ', (text or '').replace('\n', ' ')).strip()


def _mtkey(text):
    """Single canonical key for every MT lookup (must match translate_many).

    Cutting a sentence at 170 chars can leave a trailing space; without the
    final strip() the cached translation would never be found again.
    """
    return _clean(text)[:170].strip()


def _gloss(phrase):
    """Chinese for a keyword phrase; '' means it needs machine translation."""
    p = phrase.lower().strip()
    if p in TERM_ZH:
        return TERM_ZH[p]
    words = [w for w in p.split() if w and w not in ('-',)]
    parts, hit = [], 0
    for w in words:
        z = WORD_ZH.get(w) or WORD_ZH.get(w.rstrip('s'))
        if z:
            parts.append(z)
            hit += 1
        elif len(w) <= 2 and w.upper() == w:
            parts.append(w)          # keep acronyms such as AI / RL / GNN
        else:
            parts.append('')
    if hit and hit >= len([w for w in words if len(w) > 2]) * 0.6:
        return ''.join(x for x in parts if x)
    return ''


def extract_keywords(title, abstract, limit=5):
    """Return REAL technical terms, each with a Chinese gloss.

    Sliding n-grams over a headline produce noise like "spur influencer
    engagement", so candidates are restricted to: known domain phrases,
    glossary words (single or adjacent pairs) and standard acronyms. Anything
    with no Chinese gloss is handed to the MT stage instead of being shown
    as an untranslated "keyword".
    """
    title = _clean(title)
    abstract = _clean(abstract)[:1600]
    t_low, a_low = title.lower(), abstract.lower()

    # Chinese titles: prefer real dictionary terms ("深度学习", "蛋白质结构")
    # over blind n-character chunks like "深度学习在蛋白质".
    if CJK.search(title):
        rev = {}
        for en, zh in TERM_ZH.items():
            if zh not in rev or len(en) > len(rev[zh]):
                rev[zh] = en
        out, seen = [], set()
        zh_terms = sorted((zh for zh in TERM_ZH.values()
                           if zh and CJK.search(zh) and len(zh) >= 2),
                          key=len, reverse=True)
        for zh in zh_terms:
            if len(out) >= limit:
                break
            if zh in title and not any(zh in s or s in zh for s in seen):
                seen.add(zh)
                out.append({'en': rev.get(zh, ''), 'zh': zh})
        for t in CN_TOKEN_RE.findall(title):
            if len(out) >= limit:
                break
            if len(t) >= 2 and t not in ('研究', '基于', '一种', '方法', '分析') \
               and not any(t in s or s in t for s in seen):
                seen.add(t)
                out.append({'en': rev.get(t, ''), 'zh': t})
        return out[:limit]

    scores = {}

    def bump(phrase, delta):
        p = re.sub(r'\s+', ' ', (phrase or '').strip().lower()).strip(' .,:;()[]{}"\'')
        if len(p) < 2 or p in STOP or not _gloss(p):
            return
        scores[p] = scores.get(p, 0) + delta

    # 1) Known domain phrases carry the most signal.
    for phrase in TERM_ZH:
        if len(phrase) < 4:
            continue
        if phrase in t_low:
            bump(phrase, 10 + min(len(phrase.split()), 3))
        elif phrase in a_low:
            bump(phrase, 2.5 + min(a_low.count(phrase), 3) * 0.6)

    # 2) Glossary terms inside the title / abstract, plus adjacent pairs.
    def gloss_tokens(text, weight, cap):
        # Keep stopwords in the sequence so "learning OF language" never
        # becomes the bogus phrase "learning language".
        raw = [w.lower().strip("-'") for w in TOKEN_RE.findall(text)]
        cnt = {}
        for w in raw:
            if len(w) > 2 and w not in STOP and \
               (w in WORD_ZH or w.rstrip('s') in WORD_ZH):
                cnt[w] = cnt.get(w, 0) + 1
                bump(w, weight * min(cnt[w], 3))
        for a, b in zip(raw, raw[1:]):
            if a in STOP or b in STOP or a == b or len(a) < 3 or len(b) < 3:
                continue
            if (a in WORD_ZH or a.rstrip('s') in WORD_ZH) and \
               (b in WORD_ZH or b.rstrip('s') in WORD_ZH):
                bump(a + ' ' + b, weight * 1.5)
        return cap

    gloss_tokens(title, 3.4, 0)
    gloss_tokens(abstract, 0.9, 0)

    # 3) Acronyms that are themselves in the glossary (LLM, RAG, GNN ...).
    for tok in re.findall(r'\b[A-Z][A-Z0-9]{1,5}\b', title):
        low = tok.lower()
        if low in TERM_ZH or low in WORD_ZH:
            bump(low, 6)

    # Drop a shorter / singular-plural duplicate contained in a stronger one.
    def norm(p):
        return ' '.join(w.rstrip('s') for w in p.split())

    ranked = sorted(scores.items(), key=lambda kv: (-kv[1], -len(kv[0])))
    picked = []
    for phrase, sc in ranked:
        if any(phrase in p and phrase != p for p, _ in picked):
            continue
        if any(norm(phrase) == norm(p) or phrase in p or p in phrase
               for p, _ in picked):
            continue
        picked.append((phrase, sc))
        if len(picked) >= limit:
            break

    # Fallback for headlines with no domain vocabulary (industry news,
    # editorials). Prefer words the LOCAL glossary can already translate, so a
    # card stays bilingual even when the online quota is exhausted. Arbitrary
    # headline words ("reportedly", "rattlesnakes") used to be emitted with no
    # Chinese at all and showed a permanent "译…" placeholder.
    a_counts = _word_counts(a_low)
    if len(picked) < min(limit, 3):
        seen_p = [p for p, _ in picked]
        for w in TOKEN_RE.findall(title + ' ' + abstract[:700]):
            wl = w.lower().strip("-'")
            if len(wl) < 4 or wl in STOP or not _gloss(wl):
                continue
            if any(norm(wl) == norm(p) or wl in p or p in wl for p in seen_p):
                continue
            picked.append((wl, 0.9 + min(a_counts.get(wl, 0), 5) * 0.05))
            seen_p.append(wl)
            if len(picked) >= min(limit, 3):
                break

    # Only as a last resort, add untranslated title words for the MT stage.
    if len(picked) < min(limit, 3):
        words = [w for w in TOKEN_RE.findall(title)
                 if len(w) > 3 and w.lower() not in STOP]
        cand = sorted(dict.fromkeys(w.lower() for w in words),
                      key=lambda w: -(a_counts.get(w, 0) * 0.7
                                      + (2 if w[0].isupper() else 0)
                                      + len(w) / 30.0))
        for w in cand:
            if len(picked) >= min(limit, 3):
                break
            if any(norm(w) == norm(p) or w in p or p in w for p, _ in picked):
                continue
            picked.append((w, 0.5))

    out = [{'en': p, 'zh': _gloss(p), 'score': round(sc, 1)}
           for p, sc in picked]
    # Guarantee at least one Chinese keyword for EVERY result, offline or not.
    if not any(x['zh'] for x in out):
        out.insert(0, {'en': 'frontier tech', 'zh': '前沿科技',
                       'score': 0.1, 'via': 'generic'})
    return out


def _word_counts(text):
    d = {}
    for w in TOKEN_RE.findall(text):
        w = w.lower().strip("-'")
        if len(w) > 2 and w not in STOP:
            d[w] = d.get(w, 0) + 1
    return d


# ------------------------------------------------------------- free access
def free_info(item):
    """How readable for free is this hit, and is it actually a *paper*?

    Ranking target: free open-access papers first, then papers whose free
    version can be looked up, then everything else, with news / platform
    entry cards at the very bottom.
    """
    src = (item.get('source') or '').lower()
    if item.get('isPlatformCard') or item.get('entryLink'):
        return {'kind': 'entry', 'freeLevel': 'entry',
                'freeLabel': '检索入口', 'freeScore': 5}
    if src in NEWS_SOURCES:
        return {'kind': 'news', 'freeLevel': 'news',
                'freeLabel': '免费资讯', 'freeScore': 3}
    free = (item.get('isOA') or item.get('pmcid') or item.get('freePreviewUrl')
            or item.get('pdfUrl') or src in FREE_SOURCES)
    if free:
        return {'kind': 'paper', 'freeLevel': 'free',
                'freeLabel': '免费全文', 'freeScore': 0}
    if item.get('doi') or src in ('crossref', 'openalex', 'pubmed', 'nature', 'scholar'):
        return {'kind': 'paper', 'freeLevel': 'partial',
                'freeLabel': '可查免费版', 'freeScore': 1}
    return {'kind': 'paper', 'freeLevel': 'unknown',
            'freeLabel': '获取方式待确认', 'freeScore': 2}


# ----------------------------------------------------- persistent MT cache
_LOCK = threading.Lock()
_MEM = {}
_LOADED = False
_DIRTY = 0
_QUOTA_BLOCK_UNTIL = 0.0
_BLOCK_REASON = ''
_OPENER = None


def set_opener(opener):
    global _OPENER
    _OPENER = opener


def _key(text):
    return hashlib.md5(text.encode('utf-8')).hexdigest()[:20]


def _load():
    global _LOADED
    if _LOADED:
        return
    _LOADED = True
    try:
        with open(CACHE_PATH, 'r', encoding='utf-8') as f:
            data = json.load(f)
        if isinstance(data, dict):
            _MEM.update({k: v for k, v in data.items()
                         if isinstance(v, str) and v and len(v) < 600})
    except (OSError, ValueError):
        pass


def _save():
    global _DIRTY
    with _LOCK:
        if _DIRTY <= 0:
            return
        _DIRTY = 0
        snapshot = dict(_MEM)
    try:
        os.makedirs(os.path.dirname(CACHE_PATH), exist_ok=True)
        tmp = CACHE_PATH + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(snapshot, f, ensure_ascii=False)
        os.replace(tmp, CACHE_PATH)
    except OSError:
        pass


def _cache_get(text):
    _load()
    return _MEM.get(_key(text))


def _cache_put(pairs):
    global _DIRTY
    with _LOCK:
        for src, zh in pairs:
            if src and zh:
                _MEM[_key(src)] = zh
        _DIRTY += len(pairs)


def _net_json(url, timeout=11):
    req = urllib.request.Request(url, headers={'User-Agent': UA})
    op = _OPENER.open if _OPENER else urllib.request.urlopen
    with op(req, timeout=timeout) as r:
        return json.loads(r.read().decode('utf-8', 'replace'))


def _mt_batch(lines):
    """Translate a list of already-cleaned lines in one request (<=450 chars)."""
    global _QUOTA_BLOCK_UNTIL, _BLOCK_REASON
    joined = '\n'.join(lines)
    url = ('https://api.mymemory.translated.net/get?' +
           urllib.parse.urlencode({'q': joined, 'langpair': 'en|zh-CN'}))
    try:
        d = _net_json(url, timeout=12)
    except urllib.error.HTTPError as e:
        if e.code == 429:
            # Per-minute anonymous throttling is NOT the daily quota. Back off
            # briefly instead of hammering the endpoint on every enrich call;
            # the local glossary keeps every card usable in the meantime.
            _QUOTA_BLOCK_UNTIL = time.time() + 75
            _BLOCK_REASON = '译文正在优化，请稍后查看'
        return {}
    except Exception:
        return {}
    status = str(d.get('responseStatus') or '')
    details = str(d.get('responseDetails') or '')
    if status not in ('200', '') or 'QUOTA' in details.upper() or 'LIMIT' in details.upper():
        if 'QUOTA' in details.upper() or 'MYMEMORY' in details.upper():
            _QUOTA_BLOCK_UNTIL = time.time() + 1800
            _BLOCK_REASON = '译文正在优化，请稍后查看'
        return {}
    text = (d.get('responseData') or {}).get('translatedText') or ''
    got = [x.strip() for x in text.splitlines() if x.strip()]
    if len(got) != len(lines):
        return {}
    if any('QUERY LENGTH' in x or 'INVALID EMAIL' in x for x in got):
        return {}
    return dict(zip(lines, got))


def translate_many(texts, max_workers=2):
    """Return {source_text: chinese}. Untranslated entries are simply absent.

    MyMemory throttles bursts of anonymous requests, so concurrency is kept
    low and every failed chunk gets one serial second chance.
    """
    global _QUOTA_BLOCK_UNTIL
    _load()
    texts = [t for t in dict.fromkeys(_mtkey(t) for t in texts if _mtkey(t))]
    out, missing = {}, []
    for t in texts:
        hit = _cache_get(t)
        if hit:
            out[t] = hit
        else:
            missing.append(t)
    if not missing or time.time() < _QUOTA_BLOCK_UNTIL:
        return out

    # 450 chars per request keeps us below MyMemory's 500-char hard limit.
    chunks, cur, size = [], [], 0
    for t in missing:
        if cur and size + len(t) + 1 > 440:
            chunks.append(cur)
            cur, size = [], 0
        cur.append(t)
        size += len(t) + 1
    if cur:
        chunks.append(cur)

    def run(batch):
        with ThreadPoolExecutor(max_workers=min(max_workers, max(1, len(batch)))) as pool:
            futs = [pool.submit(_mt_batch, c) for c in batch]
            for f in as_completed(futs):
                try:
                    got = f.result() or {}
                except Exception:
                    continue
                if got:
                    _cache_put(list(got.items()))
                    out.update(got)

    run(chunks)
    retry = [c for c in chunks if any(t not in out for t in c)]
    if retry and time.time() >= _QUOTA_BLOCK_UNTIL:
        time.sleep(0.8)                       # let the rate limiter breathe
        for c in retry:                       # serial second chance, no burst
            if time.time() < _QUOTA_BLOCK_UNTIL:
                break
            rest = [t for t in c if t not in out]
            if not rest:
                continue
            try:
                got = _mt_batch(rest) or {}
            except Exception:
                continue
            if got:
                _cache_put(list(got.items()))
                out.update(got)
    if _DIRTY:
        _save()
    return out


_CONTEXT_FIX = (
    ('transformer', '变压器', 'Transformer'),
    ('agent', '代理', '智能体'),
    ('llm', '法学硕士', '大语言模型'),
    ('large language model', '大型语言模型', '大语言模型'),
)


def polish_translation(zh, en):
    """Fix domain terms a generic MT engine mistranslates or leaves in English.

    Only replacements whose English trigger really appears in the source are
    applied, so this can never invent a meaning that was not there.
    """
    if not zh:
        return zh
    out, low = zh, _clean(en).lower()
    for term, bad, good in _CONTEXT_FIX:
        if term in low and bad in out:
            out = out.replace(bad, good)
    for phrase in sorted((p for p in TERM_ZH if len(p) >= 9 and ' ' in p),
                         key=len, reverse=True):
        if phrase in low:
            out = re.sub(re.escape(phrase), TERM_ZH[phrase], out, flags=re.I)
    return out.strip()


def glossary_title_zh(title, keywords):
    """Honest offline fallback: Chinese keywords FROM THE TITLE, never a fake
    translated headline. Keywords mined only from the abstract used to leak in
    (a paper about "Artificial Currency" showed "基准测试"), which was worse
    than useless for quick screening."""
    low = _clean(title).lower()
    hits = []
    for k in keywords or []:
        z = (k.get('zh') or '').strip()
        en = (k.get('en') or '').lower().strip()
        if z and z not in hits and en and en in low:
            hits.append(z)
    if not hits:
        return '中英关键词速览见下方'
    return '关键词速览：' + ' · '.join(hits[:4])


def takeaway_sentences(abstract, limit=2):
    """Pick the lead + a conclusion sentence for the quick-read summary."""
    a = _clean(abstract)
    if CJK.search(a):
        parts = [p.strip() for p in re.split(r'[。！？；]', a) if len(p.strip()) > 12]
        return [p[:170] + '。' for p in parts[:limit]]
    parts = [p.strip() for p in re.split(r'(?<=[.!?])\s+', a) if len(p.strip()) > 30]
    if not parts:
        return []
    marks = ('we show', 'we demonstrate', 'we find', 'our results', 'results show',
             'we propose', 'we introduce', 'outperform', 'achieve', 'conclude',
             'suggest that', 'this work', 'we present', 'we adopted', 'we report')
    # A "However, ..." lead is a terrible one-line takeaway; start with the
    # first non-contrastive statement, then attach a conclusion sentence.
    lead = next((p for p in parts
                 if not re.match(r'^(however|while|although|but|in contrast|'
                                r'despite|nevertheless|yet)\b', p, re.I)),
                parts[0])
    def clip(s):
        s = s.strip()
        if len(s) <= 150:
            return s
        return s[:150].rsplit(' ', 1)[0].rstrip(' ,;:')

    out = [clip(lead)]
    for p in parts:
        if len(out) >= limit:
            break
        if p != lead and any(m in p.lower() for m in marks):
            out.append(clip(p))
    if len(out) < limit:
        # Prefer another plain statement over a "however, ..." contrast.
        for p in parts:
            c = clip(p)
            if c not in out and not re.search(r'\b(however|although|but|while|yet)\b', p, re.I):
                out.append(c)
                break
    if len(out) < limit:
        for p in parts:
            c = clip(p)
            if c not in out:
                out.append(c)
                break
    return out[:limit]


# ------------------------------------------------------------------ endpoint
def enrich(items, mt=False, full=False):
    """items: [{id,title,abstract,source,isOA,pdfUrl,freePreviewUrl,pmcid,doi}...]

    mt=False -> instant, fully local (keywords + Chinese gloss + free level)
    mt=True  -> additionally machine-translate titles / unknown keywords
    full=True-> also translate 1-2 takeaway sentences (immersive reader only,
                keeps the feed's first paint fast and the free quota small)
    """
    result = []
    # Titles are queued FIRST: if the free translation service throttles a
    # chunk, the headline translation still lands before optional takeaways.
    # Keywords are NEVER sent to the online service: the local glossary gives
    # every card Chinese keywords instantly, and spending a daily quota on
    # noisy headline words is both slow and unnecessary.
    mt_titles, mt_sums = [], []
    for it in items[:60]:
        title = _clean(it.get('title'))
        abstract = _clean(it.get('abstract'))
        kws = extract_keywords(title, abstract)
        entry = {
            'id': it.get('id', ''),
            'keywords': kws,
            'titleZh': '',
            'titleZhVia': '',
            'summary': takeaway_sentences(abstract) if full else [],
            'summaryZh': [],
        }
        # Every card has Chinese from the very first streamed frame: native
        # Chinese titles stay as-is, English ones get an honest local keyword
        # line. The MT stage below later upgrades them to real translations,
        # so "中文标题生成中…" never appears as a dead placeholder.
        if title and CJK.search(title):
            entry['titleZh'], entry['titleZhVia'] = title, 'native'
        elif title:
            entry['titleZh'] = glossary_title_zh(title, kws)
            entry['titleZhVia'] = 'glossary' if entry['titleZh'] else ''
        entry.update(free_info(it))
        result.append(entry)

        if not mt:
            continue
        if title and not CJK.search(title):
            mt_titles.append(_mtkey(title))
        if full:
            for s in entry['summary']:
                if not CJK.search(s):
                    mt_sums.append(_mtkey(s))

    want_mt = mt_titles + mt_sums
    stats = {'requested': 0, 'translated': 0, 'quota': False}
    if mt and want_mt:
        uniq = list(dict.fromkeys(want_mt))
        stats['requested'] = len(uniq)
        got = translate_many(uniq)
        stats['translated'] = len(got)
        stats['quota'] = time.time() < _QUOTA_BLOCK_UNTIL
        for e, it in zip(result, items[:60]):
            title = _clean(it.get('title'))
            kws = e['keywords']
            if title and not CJK.search(title):
                zh = got.get(_mtkey(title))
                if zh and 'QUERY LENGTH' not in zh:
                    e['titleZh'] = polish_translation(zh, title)
                    e['titleZhVia'] = 'mt'
            elif title and CJK.search(title):
                e['titleZh'] = title
                e['titleZhVia'] = 'native'
            e['summaryZh'] = [polish_translation(got[_mtkey(s)], s)
                              for s in e['summary'] if got.get(_mtkey(s))]
            if not e['titleZh']:
                fb = glossary_title_zh(title, kws)
                if fb:
                    e['titleZh'] = fb
                    e['titleZhVia'] = 'glossary'
    elif mt:
        for e, it in zip(result, items[:60]):
            t = _clean(it.get('title'))
            if t and CJK.search(t):
                e['titleZh'], e['titleZhVia'] = t, 'native'

    # Every card ships Chinese keywords from the very first streamed batch.
    # Untranslated candidates are dropped (they are mostly headline noise), so
    # no card ever shows a permanent "译…" placeholder — with or without quota.
    for e in result:
        e['keywords'] = [k for k in e['keywords'] if k.get('zh')]
        if not e['keywords']:
            e['keywords'] = [{'en': 'frontier tech', 'zh': '前沿科技',
                              'via': 'generic'}]

    blocked = time.time() < _QUOTA_BLOCK_UNTIL
    stats['blocked'] = blocked
    stats['quota'] = blocked or stats.get('quota', False)
    stats['note'] = _BLOCK_REASON if blocked else ''
    return {'ok': True, 'items': result, 'mt': stats}


def mt_status():
    """Live translation-channel state for the UI. Never touches the network."""
    _load()
    blocked = time.time() < _QUOTA_BLOCK_UNTIL
    return {
        'provider': '智能双语速译',
        'available': not blocked,
        'quotaUntil': int(_QUOTA_BLOCK_UNTIL) if blocked else 0,
        'cached': len(_MEM),
        'reason': _BLOCK_REASON if blocked else '',
        'fallback': '中英关键词速览',
        'note': ('正在优化译文，可先查看中英关键词速览' if blocked
                 else '智能双语速译已就绪'),
    }
