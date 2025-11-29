"""
scoring.py

Módulo de scoring / meta-score para integrarse con main.py mediante:
    import scoring
    scoring.set_callbacks(
        fetch_text_cb=fetch_homepage_text,
        whois_cb=get_domain_age_months,
        assess_quick_cb=assess_domain_quality_quick,
        domain_alive_short_cb=domain_alive_short,
        dynamic_blacklist_lookup=domain_is_dynamic_blacklisted
    )
    scoring.set_config(...)

Incluye:
 - Normalización de componentes (0-100 ranges específicos)
 - Confidence (variance) y reglas de aceptación combinadas
 - Penalización spam en fast_filter (más agresiva y atenuada por whitelist)
 - EWMA histórico por dominio (domain_quality_ewma)
 - Decay / freshness heuristics (copyright year heuristic + whois age decay)
 - Escalado logístico / saturación (sigmoid) para combinar componentes
 - HTTPS / certificado check (bonus si valido)
 - Source weighting (motor origen)
 - Dynamic blacklist handling con path de recuperación
 - Content_quality extraction (p_count, meta, ld+json, content_len)
 - Telemetría simple: alerta si la media de meta_scores cae >10% respecto a baseline
 - Minimum-components safeguard (min_required components)
 - A/B / canary experiment framework mínimo (dos sets de pesos, recogida de métricas)
"""

from typing import List, Optional, Tuple, Dict, Any, Callable
import time
import logging
import re
import random
import math
import threading
import json
import os
import functools

# optional deps
try:
    from sklearn.feature_extraction.text import TfidfVectorizer
    import numpy as np
    _SKLEARN_OK = True
except Exception:
    _SKLEARN_OK = False

try:
    import requests
    from requests.exceptions import SSLError
    _REQUESTS_OK = True
except Exception:
    requests = None
    _REQUESTS_OK = False

try:
    from bs4 import BeautifulSoup
    _BS4_OK = True
except Exception:
    _BS4_OK = False

# ---------------- callbacks & config injection (desde main.py) ----------------
_fetch_text_cb: Optional[Callable[[str, float], Optional[str]]] = None
_whois_cb: Optional[Callable[[str], Optional[int]]] = None
_assess_quick_cb: Optional[Callable[[str, int], Tuple[int, List[str]]]] = None
_domain_alive_short_cb: Optional[Callable[[str], bool]]] = None  # type: ignore
_dynamic_blacklist_lookup: Optional[Callable[[str], bool]] = None

def set_callbacks(fetch_text_cb=None, whois_cb=None, assess_quick_cb=None, domain_alive_short_cb=None, dynamic_blacklist_lookup=None):
    global _fetch_text_cb, _whois_cb, _assess_quick_cb, _domain_alive_short_cb, _dynamic_blacklist_lookup
    _fetch_text_cb = fetch_text_cb
    _whois_cb = whois_cb
    _assess_quick_cb = assess_quick_cb
    _domain_alive_short_cb = domain_alive_short_cb
    _dynamic_blacklist_lookup = dynamic_blacklist_lookup

_CONF: Dict[str, Any] = {
    "TRUSTED_WHITELIST": set(),
    "SOCIAL_BLACKLIST": set(),
    "SUSPICIOUS_TLDS": set(("xyz", "top", "club", "online", "pw", "tk", "loan", "win")),
    "QUALITY_ACCEPT": 80,    # meta acceptance target default (matches new rules)
    "QUALITY_WARN": 40,
    "FAST_ACCEPT_THRESHOLD": 50,
    "FAST_REJECT_THRESHOLD": 40,
    "BLACKLIST_MIN_REJECTS": 2,
    # EWMA alpha for domain history
    "EWMA_ALPHA": 0.2,
    # thresholds and mins
    "MIN_SUBTASKS_REQUIRED": 1,
    "MIN_CONFIDENCE_REQUIRED": 0.4,
    # experiment defaults
    "EXPERIMENT_SAMPLE_RATE": 0.1,
    # telemetry file (optional) - if set persists EWMA/metrics
    "PERSISTENCE_PATH": os.environ.get("SCORING_PERSIST_PATH", ""),
}

def set_config(**kwargs):
    for k, v in kwargs.items():
        _CONF[k] = v

# ---------------- internal state (thread-safe) ----------------
_state_lock = threading.Lock()
_domain_quality_ewma: Dict[str, float] = {}   # root_domain -> ewma score 0..100
_experiment_stats: Dict[str, Dict[str, Any]] = {}
_score_history: List[float] = []  # rolling recent meta_scores for telemetry
_baseline_mean: Optional[float] = None
_baseline_ts: Optional[float] = None

_PERSIST_FILE = _CONF.get("PERSISTENCE_PATH") or None
if not _PERSIST_FILE:
    _PERSIST_FILE = None

def _persist_state():
    """Persist EWMA & experiments if persistence path provided."""
    path = _PERSIST_FILE
    if not path:
        return
    try:
        with _state_lock:
            data = {"ewma": _domain_quality_ewma, "experiments": _experiment_stats, "baseline_mean": _baseline_mean, "baseline_ts": _baseline_ts}
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f)
        os.replace(tmp, path)
    except Exception as e:
        logging.debug("scoring: persist failed: %s", e)

def _load_state():
    path = _PERSIST_FILE
    if not path:
        return
    try:
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            with _state_lock:
                global _domain_quality_ewma, _experiment_stats, _baseline_mean, _baseline_ts
                _domain_quality_ewma.update(data.get("ewma", {}))
                _experiment_stats.update(data.get("experiments", {}))
                _baseline_mean = data.get("baseline_mean", _baseline_mean)
                _baseline_ts = data.get("baseline_ts", _baseline_ts)
    except Exception as e:
        logging.debug("scoring: load state failed: %s", e)

_load_state()

# ---------------- utility: safe regex findall ----------------
@functools.lru_cache(maxsize=512)
def _ensure_re(pat, flags=0):
    return re.compile(pat, flags)

def safe_findall(pat, text):
    try:
        cre = _ensure_re(pat, re.I)
        return cre.findall(text or "")
    except Exception:
        return []

# ---------------- normalization helpers ----------------
def normalize_component(value: float, in_min: float, in_max: float, out_min: float = 0.0, out_max: float = 100.0) -> float:
    """Normalize a component from [in_min,in_max] to [out_min,out_max] and clamp."""
    try:
        v = float(value)
        if in_max == in_min:
            return float(out_max)
        ratio = (v - in_min) / (in_max - in_min)
        mapped = out_min + ratio * (out_max - out_min)
        return max(out_min, min(out_max, mapped))
    except Exception:
        return float(out_min)

def logistic(x: float, k: float = 1.0, x0: float = 50.0) -> float:
    """Logistic-like saturation mapping centered at x0, returns 0..1"""
    try:
        return 1.0 / (1.0 + math.exp(-k * (x - x0) / 10.0))
    except Exception:
        return 0.0 if x < x0 else 1.0

# alternative gentle saturation
def saturate_x_over_1_plus_x(x: float) -> float:
    try:
        return x / (1.0 + x)
    except Exception:
        return 0.0

# ---------------- tfidf_similarity (exported) ----------------
def tfidf_similarity(a: str, b: str) -> float:
    a = (a or "").strip()
    b = (b or "").strip()
    if not a or not b:
        return 0.0
    if _SKLEARN_OK:
        try:
            vec = TfidfVectorizer(ngram_range=(1,2), max_features=4000).fit([a, b])
            m = vec.transform([a, b])
            A = m.toarray()[0]
            B = m.toarray()[1]
            num = float((A * B).sum())
            denom = (float((A*A).sum())**0.5) * (float((B*B).sum())**0.5) + 1e-9
            return float(num / denom) if denom > 0 else 0.0
        except Exception as e:
            logging.debug("scoring.tfidf sklearn fallback: %s", e)
    ta = set(safe_findall(r"[A-Za-zÀ-ÿ0-9]{3,}", a.lower()))
    tb = set(safe_findall(r"[A-Za-zÀ-ÿ0-9]{3,}", b.lower()))
    if not ta or not tb:
        return 0.0
    inter = ta.intersection(tb)
    return len(inter) / float(max(len(ta), len(tb)))

# ---------------- fast_filter (mejorado con spam_penalty) ----------------
def fast_filter(prompt: str, domain: str, keywords: Optional[List[str]] = None) -> Tuple[int, List[str], str]:
    score = 50
    reasons: List[str] = []
    if not domain:
        return 0, ["no-domain"], "reject"
    d = domain.lower().strip()
    parts = d.split(".")
    tld = parts[-1] if len(parts) > 1 else ""
    social_blacklist = set(_CONF.get("SOCIAL_BLACKLIST") or [])
    suspicious_tlds = set(_CONF.get("SUSPICIOUS_TLDS") or set())
    trusted_whitelist = set(_CONF.get("TRUSTED_WHITELIST") or set())

    # heavy penalty if social
    if any(d.endswith(s) for s in social_blacklist):
        reasons.append("Social domain")
        score -= 90
        return max(0, score), reasons, "reject"

    # suspicious tld
    if tld in suspicious_tlds:
        reasons.append(f"Suspicious TLD .{tld}")
        score -= 25

    # dynamic blacklist via callback
    try:
        if _dynamic_blacklist_lookup and _dynamic_blacklist_lookup(domain):
            reasons.append("Dynamic blacklist hit")
            score -= 45
    except Exception:
        logging.debug("dynamic_blacklist_lookup error for %s", domain)

    # token overlap
    try:
        domain_tokens = set(safe_findall(r"[A-Za-z0-9]{3,}", d))
        prompt_tokens = set()
        if keywords:
            for k in keywords:
                prompt_tokens.update(safe_findall(r"[A-Za-z0-9]{3,}", (k or "").lower()))
        else:
            prompt_tokens.update(safe_findall(r"[A-Za-zÀ-ÿ0-9]{3,}", (prompt or "").lower()))
        overlap = domain_tokens.intersection(prompt_tokens)
        overlap_score = min(len(overlap) * 6, 30)
        if overlap:
            reasons.append(f"Token overlap: {', '.join(list(overlap)[:6])}")
            score += overlap_score
    except Exception:
        pass

    # spammy patterns (más agresivos)
    spam_patterns = [
        r"(cheap|free[- ]?download|get[- ]?paid|captcha|proxy|clickbait|earn money|make money|work from home|millionaire)\b",
        r"(viagra|casino|porn|adult|sex|loan|creditcard|bitcoin|cryptocurrency)\b",
        r"(click here|buy now|limited time offer)\b"
    ]
    spam_penalty = 0
    for p in spam_patterns:
        try:
            if re.search(p, domain, re.I) or re.search(p, prompt or "", re.I):
                spam_penalty += 40
        except Exception:
            continue
    # adjust spam penalty if whitelisted
    if (domain in trusted_whitelist) or any(domain.endswith("." + w) for w in trusted_whitelist):
        spam_penalty = max(0, spam_penalty - 30)
        if spam_penalty > 0:
            reasons.append("Spam pattern (whitelist attenuated)")
    elif spam_penalty > 0:
        reasons.append("Spam pattern")
    score -= spam_penalty

    # final whitelist boost
    if domain in trusted_whitelist or any(domain.endswith("." + t) for t in trusted_whitelist):
        reasons.append("Trusted whitelist")
        score += 40

    score = max(0, min(100, int(score)))
    FAST_ACCEPT_THRESHOLD = int(_CONF.get("FAST_ACCEPT_THRESHOLD", 50))
    FAST_REJECT_THRESHOLD = int(_CONF.get("FAST_REJECT_THRESHOLD", 40))
    if score >= FAST_ACCEPT_THRESHOLD:
        verdict = "accept"
    elif score <= FAST_REJECT_THRESHOLD:
        verdict = "reject"
    else:
        verdict = "maybe"
    return int(score), reasons, verdict

# ---------------- content quality extractor (0..30) ----------------
def compute_content_quality_from_html(text: str) -> Tuple[float, List[str]]:
    reasons: List[str] = []
    if not text:
        return 0.0, reasons
    try:
        if _BS4_OK:
            soup = BeautifulSoup(text, "html.parser")
            p_count = len(soup.find_all("p"))
            has_meta = bool(soup.find("meta", attrs={"name": "description"}))
            has_ld = bool(soup.find("script", type="application/ld+json") or soup.find(attrs={"itemtype": re.compile(r"schema.org", re.I)}))
            content_len = len(soup.get_text(" ", strip=True))
            # score composition
            score = 0.0
            # p_count contribution up to 12 pts
            score += min(12.0, float(p_count) * 1.5)
            # meta description up to 6 pts
            if has_meta:
                score += 6.0
            # ld+json up to 6 pts
            if has_ld:
                score += 6.0
            # content length up to 6 pts (cap)
            score += min(6.0, min(5000, content_len) / 1000.0 * 1.2)
            if p_count:
                reasons.append(f"p_count={p_count}")
            if has_meta:
                reasons.append("has_meta")
            if has_ld:
                reasons.append("has_ldjson")
            return float(min(30.0, score)), reasons
        else:
            # fallback: basic heuristics on text
            toks = safe_findall(r"\w{4,}", text)
            clen = len(toks)
            score = min(30.0, (min(300, clen) / 300.0) * 30.0)
            if clen:
                reasons.append(f"tokens={clen}")
            return float(score), reasons
    except Exception as e:
        logging.debug("compute_content_quality error: %s", e)
        return 0.0, []

# ---------------- https / ssl quick validator ----------------
def https_certificate_ok(domain: str, timeout: float = 3.0) -> bool:
    if not _REQUESTS_OK:
        return False
    try:
        url = f"https://{domain}/"
        # head with verify True will raise SSLError on cert issues
        r = requests.head(url, timeout=timeout, allow_redirects=True, verify=True, headers={"User-Agent": "scoring/1.0"})
        ok = getattr(r, "status_code", 0) < 500
        try:
            if r is not None:
                r.close()
        except Exception:
            pass
        return bool(ok)
    except SSLError:
        return False
    except Exception:
        return False

# ---------------- EWMA helpers ----------------
def update_domain_ewma(domain: str, new_score: float):
    root = domain.lower().strip()
    alpha = float(_CONF.get("EWMA_ALPHA", 0.2))
    with _state_lock:
        old = _domain_quality_ewma.get(root, None)
        if old is None:
            _domain_quality_ewma[root] = float(new_score)
        else:
            _domain_quality_ewma[root] = alpha * float(new_score) + (1 - alpha) * float(old)
    # persist occasionally
    try:
        _persist_state()
    except Exception:
        pass

def get_domain_ewma(domain: str) -> Optional[float]:
    root = domain.lower().strip()
    with _state_lock:
        return _domain_quality_ewma.get(root)

# ---------------- experiment framework (A/B minimal) ----------------
def setup_experiment(name: str, weights_a: Dict[str, float], weights_b: Dict[str, float], sample_rate: float = None):
    """Register an experiment with two weight sets. sample_rate in 0..1."""
    if sample_rate is None:
        sample_rate = float(_CONF.get("EXPERIMENT_SAMPLE_RATE", 0.0))
    with _state_lock:
        _experiment_stats[name] = {
            "weights_a": weights_a,
            "weights_b": weights_b,
            "sample_rate": float(sample_rate),
            "counters": {"a": 0, "b": 0, "none": 0},
            "results": {"a": [], "b": []}
        }
    _persist_state()

def _pick_experiment_variant(name: str) -> str:
    with _state_lock:
        exp = _experiment_stats.get(name)
        if not exp:
            return "none"
        if random.random() < exp.get("sample_rate", 0.0):
            # choose randomly a or b
            variant = "a" if random.random() < 0.5 else "b"
            exp["counters"][variant] = exp["counters"].get(variant, 0) + 1
            return variant
        else:
            exp["counters"]["none"] = exp["counters"].get("none", 0) + 1
            return "none"

def _record_experiment_result(name: str, variant: str, score: float):
    if not name or variant == "none":
        return
    with _state_lock:
        exp = _experiment_stats.get(name)
        if not exp:
            return
        exp["results"].setdefault(variant, []).append(float(score))
    _persist_state()

def get_experiment_summary(name: str) -> Dict[str, Any]:
    with _state_lock:
        exp = _experiment_stats.get(name, {})
        res = {"counters": exp.get("counters", {}), "means": {}}
        for v in ("a", "b"):
            arr = exp.get("results", {}).get(v, [])
            res["means"][v] = (sum(arr) / len(arr)) if arr else None
        return res

# ---------------- telemetry: distribution drift alert ----------------
def _update_score_history_and_alert(score: float):
    global _baseline_mean, _baseline_ts
    with _state_lock:
        _score_history.append(float(score))
        # cap history to reasonable length
        if len(_score_history) > 5000:
            _score_history[:] = _score_history[-5000:]
        # compute mean of last N (e.g., 100)
        window = _score_history[-200:] if len(_score_history) >= 200 else list(_score_history)
        mean_now = (sum(window) / len(window)) if window else None
        now = time.time()
        # establish baseline if none or older than a day
        if _baseline_mean is None or (_baseline_ts and now - _baseline_ts > 86400):
            _baseline_mean = mean_now
            _baseline_ts = now
            try:
                _persist_state()
            except Exception:
                pass
            return
        # if mean_now dropped >10% relative to baseline_mean -> alert
        try:
            if mean_now is not None and _baseline_mean and mean_now < 0.9 * _baseline_mean:
                logging.warning("Telemetry alert: mean meta_score dropped from %.2f to %.2f (>10%% drop).", _baseline_mean, mean_now)
                # update baseline to avoid repeated alerts; keep timestamp
                _baseline_mean = mean_now
                _baseline_ts = now
                try:
                    _persist_state()
                except Exception:
                    pass
        except Exception:
            pass

# ---------------- meta-score combiner ----------------
def compute_meta_score(components: Dict[str, float], source_engine: str = "ddg", domain: str = "", experiment_weights: Optional[Dict[str, float]] = None) -> Tuple[float, Dict[str, float]]:
    """
    Combine normalized components into a meta score using:
     - normalizations per component
     - optional logistic/saturation to avoid dominance
     - source_engine_weight multiplier applied at end (small)
    Returns (meta_score_0_100, normalized_components_map)
    components expected keys: tfidf (0..1), assess_quick (0..100),
                             whois_age_months (int), head_ok (bool/0-1),
                             fast_filter (0..100), content_quality (0..30), https_ok (0/1)
    """
    # normalization targets per spec:
    # TFIDF -> [0,40] (input 0..1)
    # assess_quick -> map 0..100 to [0..40]
    # whois_age_months -> map 0..120+ to [0..15]
    # head_check -> {0,6}
    # fast_filter -> 0..100 -> [0..40] (but spam penalty already applied)
    # content_quality -> 0..30 -> [0..30]
    # https_ok -> boolean -> [0..5]
    try:
        tfidf_in = float(components.get("tfidf", 0.0))
        assess_in = float(components.get("assess_quick", 0.0))
        whois_in = float(components.get("whois_age_months", 0.0)) if components.get("whois_age_months") is not None else 0.0
        head_in = 6.0 if components.get("head_ok") else 0.0
        fast_in = float(components.get("fast_filter", 0.0))
        content_in = float(components.get("content_quality", 0.0))
        https_in = 5.0 if components.get("https_ok") else 0.0

        n_tfidf = normalize_component(tfidf_in * 100.0, 0.0, 100.0, 0.0, 40.0)  # tfidf 0..1 -> x100 -> map 0..100 to 0..40
        n_assess = normalize_component(assess_in, 0.0, 100.0, 0.0, 40.0)
        n_whois = normalize_component(min(whois_in, 240.0), 0.0, 120.0, 0.0, 15.0)  # saturate at 120 months
        n_head = normalize_component(head_in, 0.0, 6.0, 0.0, 6.0)
        n_fast = normalize_component(fast_in, 0.0, 100.0, 0.0, 40.0)
        n_content = normalize_component(content_in, 0.0, 30.0, 0.0, 30.0)
        n_https = normalize_component(https_in, 0.0, 5.0, 0.0, 5.0)

        normalized = {
            "tfidf": n_tfidf,
            "assess_quick": n_assess,
            "whois": n_whois,
            "head": n_head,
            "fast": n_fast,
            "content": n_content,
            "https": n_https
        }

        # default weights
        base_weights = {
            "tfidf": 0.22,
            "assess_quick": 0.20,
            "whois": 0.12,
            "head": 0.06,
            "fast": 0.20,
            "content": 0.15,
            "https": 0.05
        }
        # if experiment weights provided override base_weights
        if experiment_weights:
            for k, v in experiment_weights.items():
                if k in base_weights:
                    base_weights[k] = float(v)

        # compute weighted sum but apply saturation per-component
        comp_vals = {}
        accum = 0.0
        for k, w in base_weights.items():
            raw = normalized.get(k, 0.0)
            # apply mild logistic saturation centered at half of component range
            sat = logistic(raw, k=0.08, x0=( (0.0 + (40.0 if k in ("tfidf","assess_quick","fast") else (30.0 if k=="content" else 15.0)) ) / 2.0 ))
            # we blend linear raw and saturated form to preserve monotonicity:
            blended = 0.6 * (raw / 100.0) + 0.4 * sat  # both in 0..1 roughly
            comp_vals[k] = blended * 100.0  # normalized to 0..100 scale
            accum += w * comp_vals[k]

        # apply source_engine weighting
        source_weights = {"gsearch":1.0, "ddg":0.9, "searx":0.85, "scrape":0.6}
        sw = source_weights.get(source_engine, 0.85)
        meta_raw = accum * sw

        # apply final saturation (x/(1+x)) to avoid runaway and map back to 0..100
        meta_scaled = saturate_x_over_1_plus_x(meta_raw / 100.0) * 100.0

        # clamp
        meta_score = max(0.0, min(100.0, float(meta_scaled)))

        return meta_score, normalized

    except Exception as e:
        logging.debug("compute_meta_score error: %s", e)
        return 0.0, {}

# ---------------- heavy_check avanzado (usa compute_meta_score, confidence, min-components, dynamic blacklist logic, experiments) ----------------
def heavy_check(prompt: str, domain: str, keywords: Optional[List[str]] = None, source_engine: str = "ddg", experiment_name: Optional[str] = None) -> Dict[str, Any]:
    start = time.time()
    reasons: List[str] = []
    subtask_results = {"whois": None, "fetch_text": None, "assess_quick": None, "head_check": None}
    subtask_successes = 0

    # schedule subtasks using callbacks if available; fallback to None-type behavior (light)
    with threading.Lock():
        # WhoIs
        whois_val = None
        try:
            if _whois_cb:
                whois_val = _whois_cb(domain)
                subtask_results["whois"] = whois_val
                if whois_val is not None:
                    subtask_successes += 1
                    reasons.append(f"whois-age-months={whois_val}")
        except Exception as e:
            logging.debug("heavy_check whois cb error %s", e)

        # fetch text
        text = None
        try:
            if _fetch_text_cb:
                text = _fetch_text_cb(domain, float( (6.0) ))
                subtask_results["fetch_text"] = text
                if text and isinstance(text, str) and len(text) > 40:
                    subtask_successes += 1
                    reasons.append("fetched homepage text")
            else:
                # cannot do network here; leave as None
                subtask_results["fetch_text"] = None
        except Exception as e:
            logging.debug("heavy_check fetch_text cb error %s", e)

        # assess_quick
        try:
            if _assess_quick_cb:
                aq = _assess_quick_cb(domain, int(6))
                subtask_results["assess_quick"] = aq
                if isinstance(aq, tuple) and aq[0] is not None:
                    subtask_successes += 1
                    reasons.extend((aq[1] or [])[:3])
            else:
                subtask_results["assess_quick"] = None
        except Exception as e:
            logging.debug("heavy_check assess_quick cb error %s", e)

        # head_check short
        try:
            head_ok = False
            if _domain_alive_short_cb:
                head_ok = bool(_domain_alive_short_cb(domain))
            else:
                head_ok = False
            subtask_results["head_check"] = head_ok
            if head_ok:
                subtask_successes += 1
                reasons.append("head-check OK")
        except Exception as e:
            logging.debug("heavy_check head cb error %s", e)

    # compute components
    components: Dict[str, float] = {}
    # whois months
    try:
        components["whois_age_months"] = int(subtask_results.get("whois") or 0)
    except Exception:
        components["whois_age_months"] = 0

    # assess_quick score
    try:
        aq = subtask_results.get("assess_quick")
        if isinstance(aq, tuple):
            components["assess_quick"] = float(aq[0])
        else:
            components["assess_quick"] = 0.0
    except Exception:
        components["assess_quick"] = 0.0

    # fetch text based features: tfidf + content_quality + freshness heuristics
    text_val = subtask_results.get("fetch_text")
    if text_val and isinstance(text_val, str) and len(text_val) > 40:
        try:
            sim = tfidf_similarity(prompt, text_val)
            components["tfidf"] = float(sim)  # 0..1
        except Exception:
            components["tfidf"] = 0.0
        try:
            cqual, c_reasons = compute_content_quality_from_html(text_val)
            components["content_quality"] = float(cqual)
            if c_reasons:
                reasons.extend(c_reasons[:2])
        except Exception:
            components["content_quality"] = 0.0
        # freshness heuristics: look for copyright year / "updated" tokens
        try:
            yrs = safe_findall(r"©\s*([12][0-9]{3})", text_val)
            if yrs:
                try:
                    latest = max(int(y) for y in yrs)
                    cy = time.gmtime().tm_year
                    if latest >= cy:
                        reasons.append("fresh-copyright")
                        components["freshness_bonus"] = 5.0
                    elif latest < cy - 3:
                        reasons.append("old-copyright")
                        components["freshness_bonus"] = -4.0
                except Exception:
                    pass
        except Exception:
            pass
    else:
        components["tfidf"] = 0.0
        components["content_quality"] = 0.0
        components["freshness_bonus"] = 0.0

    # head ok
    components["head_ok"] = 1.0 if subtask_results.get("head_check") else 0.0

    # fast_filter (use local fast_filter to compute quick score)
    try:
        ff_score, ff_reasons, ff_verdict = fast_filter(prompt, domain, keywords)
        components["fast_filter"] = float(ff_score)
        reasons.extend(ff_reasons[:2])
    except Exception:
        components["fast_filter"] = 0.0

    # https check
    try:
        https_ok = https_certificate_ok(domain)
        components["https_ok"] = 1.0 if https_ok else 0.0
        if https_ok:
            reasons.append("https_ok")
    except Exception:
        components["https_ok"] = 0.0

    # apply freshness bonus if present
    try:
        fb = float(components.get("freshness_bonus", 0.0))
    except Exception:
        fb = 0.0

    # Experiment variant pick (A/B)
    variant = "none"
    exp_weights = None
    if experiment_name and experiment_name in _experiment_stats:
        variant = _pick_experiment_variant(experiment_name)
        with _state_lock:
            exp = _experiment_stats.get(experiment_name)
            if exp and variant in ("a", "b"):
                exp_weights = exp.get("weights_a" if variant == "a" else "weights_b")

    # Compute meta_score and normalized components
    meta_score, normalized = compute_meta_score(
        {
            "tfidf": components.get("tfidf", 0.0),
            "assess_quick": components.get("assess_quick", 0.0),
            "whois_age_months": components.get("whois_age_months", 0.0),
            "head_ok": components.get("head_ok", 0.0),
            "fast_filter": components.get("fast_filter", 0.0),
            "content_quality": components.get("content_quality", 0.0),
            "https_ok": components.get("https_ok", 0.0)
        },
        source_engine=source_engine,
        domain=domain,
        experiment_weights=exp_weights
    )

    # incorporate freshness bonus additively (small)
    meta_score = min(100.0, max(0.0, meta_score + fb))

    # Confidence: count how many components contributed materially (> small epsilon) / total_components
    contrib_count = 0
    total_components = 7  # tfidf, assess_quick, whois, head, fast, content, https
    for k, v in normalized.items():
        if float(v) > 3.0:  # component considered "contributed"
            contrib_count += 1
    confidence = float(contrib_count) / float(total_components) if total_components else 0.0

    # Minimum-components safeguard
    min_req = int(_CONF.get("MIN_SUBTASKS_REQUIRED", 1))
    min_conf_req = float(_CONF.get("MIN_CONFIDENCE_REQUIRED", 0.4))
    if subtask_successes < min_req and confidence < min_conf_req:
        reasons.append("min-components-failed")
        # strong penalty
        meta_score = meta_score * 0.45

    # Dynamic blacklist adaptive handling
    try:
        if _dynamic_blacklist_lookup and _dynamic_blacklist_lookup(domain):
            ewma = get_domain_ewma(domain) or 0.0
            if ewma < 60.0:
                reasons.append("dynamic-blacklist-penalty")
                meta_score = max(0.0, meta_score - 30.0)
            else:
                reasons.append("dynamic-blacklist-recovery-allowed")
                # allow but require higher confidence threshold later (handled by acceptance rules)
    except Exception:
        pass

    # Confidence-aware acceptance rules
    accept = False
    if meta_score >= float(_CONF.get("QUALITY_ACCEPT", 80)):
        accept = True
    elif meta_score >= 65.0 and confidence >= 0.75:
        accept = True
    else:
        accept = False

    # update EWMA history for the domain (smoothed)
    try:
        update_domain_ewma(domain, meta_score)
    except Exception:
        pass

    # telemetry update
    try:
        _update_score_history_and_alert(meta_score)
    except Exception:
        pass

    # record experiment if any
    try:
        if experiment_name:
            _record_experiment_result(experiment_name, variant, meta_score)
    except Exception:
        pass

    # record summary
    elapsed = time.time() - start
    result = {
        "score": int(round(meta_score)),
        "meta_score": meta_score,
        "normalized_components": normalized,
        "confidence": round(confidence, 3),
        "contrib_components": contrib_count,
        "subtask_successes": subtask_successes,
        "verdict": ("accept" if accept else ("maybe" if meta_score >= int(_CONF.get("QUALITY_WARN", 40)) else "reject")),
        "reasons": reasons[:12],
        "elapsed": elapsed,
        "variant": variant
    }
    return result

# ---------------- simple exported helpers ----------------
__all__ = [
    "set_callbacks", "set_config",
    "tfidf_similarity", "fast_filter", "compute_content_quality_from_html",
    "heavy_check", "setup_experiment", "get_experiment_summary", "compute_meta_score",
    "get_domain_ewma"
]
