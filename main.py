# -*- coding: utf-8 -*-
"""
main.py - Domain-only search app (prompt -> queries -> domains)
Versión con protección contra ReDoS, límite de prompt (5000), rechazo de "palabras gigantes",
y demás mejoras integradas y coordinadas.
"""
import os
import re
import time
import random
import logging
import json
import threading
import concurrent.futures
from typing import List, Optional, Tuple, Dict, Any
from urllib.parse import urlparse, quote_plus
import socket
import ipaddress
import functools
import urllib.robotparser as robotparser
from datetime import timedelta
import collections

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from bs4 import BeautifulSoup
from flask import Flask, request, render_template_string, Response, jsonify

# optional idna (punycode) - fallback safe behavior if falta
try:
    import idna
except Exception:
    idna = None

# Optional libs (graceful fallback)
try:
    import whois as whois_lib
    try:
        logging.getLogger("whois").setLevel(logging.CRITICAL)
        logging.getLogger("whois.whois").setLevel(logging.CRITICAL)
        logging.getLogger("whois").propagate = False
    except Exception:
        pass
except Exception:
    whois_lib = None

try:
    import tldextract
except Exception:
    tldextract = None

# NLP optional
try:
    import spacy
    try:
        _nlp = spacy.load("es_core_news_sm")
    except Exception:
        try:
            _nlp = spacy.load("en_core_web_sm")
        except Exception:
            _nlp = None
except Exception:
    spacy = None
    _nlp = None

# TF-IDF optional
_TFIDF_OK = False
try:
    from sklearn.feature_extraction.text import TfidfVectorizer
    import numpy as np
    _TFIDF_OK = True
except Exception:
    _TFIDF_OK = False

# Search backends detection
_GSEARCH_OK = False
try:
    from googlesearch import search as gsearch_func
    _GSEARCH_OK = True
    logging.info("googlesearch available")
except Exception:
    gsearch_func = None

_DDG_OK = False
_DDGS_CLASS = None
try:
    from ddgs import DDGS as _DDGS_CLASS
    _DDG_OK = True
    logging.info("ddgs available")
except Exception:
    try:
        from duckduckgo_search import DDGS as _DDGS_CLASS
        _DDG_OK = True
        logging.info("duckduckgo_search available")
    except Exception:
        _DDGS_CLASS = None
        _DDG_OK = False

# ---------------- Config + env ----------------
PORT = int(os.environ.get("PORT", 10000))
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7)",
    "Mozilla/5.0 (X11; Linux x86_64)",
    "Mozilla/5.0 (iPhone; CPU iPhone OS 16_0 like Mac OS X)",
]
HEADERS_BASE = {"Accept-Language": "es-ES,es;q=0.9,en;q=0.8", "Connection": "keep-alive", "Cache-Control": "no-cache"}
DEFAULT_TIMEOUT = int(os.environ.get("DEFAULT_TIMEOUT", "8"))
HEAD_TIMEOUT = int(os.environ.get("HEAD_TIMEOUT", "4"))
JITTER_BETWEEN_QUERIES = (float(os.environ.get("JITTER_MIN", "1.0")), float(os.environ.get("JITTER_MAX", "3.0")))
JITTER_BETWEEN_PAGES = (float(os.environ.get("JITTER_P_MIN", "0.2")), float(os.environ.get("JITTER_P_MAX", "0.8")))
MAX_BACKOFF = int(os.environ.get("MAX_BACKOFF", "600"))
SEARX_INSTANCES = os.environ.get("SEARX_INSTANCES", "https://searx.tiekoetter.com,https://searx.org").split(",")
MAX_CYCLES = int(os.environ.get("MAX_CYCLES", "12"))

# Prompt safety limits (NUEVAS CONFIGURACIONES)
PROMPT_MAX_CHARS = int(os.environ.get("PROMPT_MAX_CHARS", "5000"))   # si excede, se recorta
PROMPT_MAX_WORD = int(os.environ.get("PROMPT_MAX_WORD", "300"))     # si existe palabra > esto -> rechazar

# ReDoS / safe-regex config
SAFE_REGEX_MAX_INPUT = int(os.environ.get("SAFE_REGEX_MAX_INPUT", "2000"))  # longitud máxima a aplicar regex
_SAFE_RE_COMPILE_CACHE_SIZE = int(os.environ.get("SAFE_RE_CACHE_SIZE", "256"))

# Robots.txt: NO CACHE configured by user requirement -> always fetch fresh
ROBOTS_BYPASS_HOSTS = set(
    h.strip().lower()
    for h in os.environ.get(
        "ROBOTS_BYPASS_HOSTS",
        "www.google.com,google.com,www.bing.com,bing.com,duckduckgo.com,ddg.gg,searx.tiekoetter.com,searx.org"
    ).split(",")
    if h.strip()
)

# Quality thresholds
QUALITY_TARGET = int(os.environ.get("QUALITY_TARGET", "80"))
QUALITY_ACCEPT = int(os.environ.get("QUALITY_ACCEPT", "50"))
QUALITY_WARN = int(os.environ.get("QUALITY_WARN", "40"))
BLACKLIST_FILE = os.environ.get("BLACKLIST_FILE", "blacklist.json")
BLACKLIST_MIN_REJECTS = int(os.environ.get("BLACKLIST_MIN_REJECTS", "2"))

TRUSTED_WHITELIST = set(os.environ.get("TRUSTED_WHITELIST", "wikipedia.org,elpais.com,bbc.com,nytimes.com,medium.com,harvard.edu,stanford.edu").split(","))
SOCIAL_BLACKLIST = set(os.environ.get("SOCIAL_BLACKLIST", "facebook.com,instagram.com,twitter.com,x.com,pinterest.com,linkedin.com,tiktok.com,youtube.com,youtu.be,reddit.com,tumblr.com").split(","))

# concurrency + tuning
MAX_WORKERS = int(os.environ.get("MAX_WORKERS", "28"))
HTTP_CONCURRENCY = int(os.environ.get("HTTP_CONCURRENCY", "12"))
HEAVY_TIMEOUT_SECS = int(os.environ.get("HEAVY_TIMEOUT_SECS", "12"))
FAST_ACCEPT_THRESHOLD = int(os.environ.get("FAST_ACCEPT_THRESHOLD", str(QUALITY_ACCEPT)))
FAST_REJECT_THRESHOLD = int(os.environ.get("FAST_REJECT_THRESHOLD", str(QUALITY_WARN)))
OVERSHOOT_FACTOR = float(os.environ.get("OVERSHOOT_FACTOR", "2.0"))

# Proxy/env settings for http_request wrapper (optional)
PROXY_LIST_FILE = os.environ.get("PROXY_LIST_FILE", "")
PROXY_LIST_STR = os.environ.get("PROXY_LIST", "")
PROXY_ROTATION_MODE = os.environ.get("PROXY_ROTATION_MODE", "random")  # random | roundrobin | latency
PROXY_HEALTH_CHECK_INTERVAL = int(os.environ.get("PROXY_HEALTH_CHECK_INTERVAL", "45"))  # seconds
PROXY_HEALTH_TEST_URL = os.environ.get("PROXY_HEALTH_TEST_URL", "https://httpbin.org/ip")
PROXY_MAX_FAILURES_BEFORE_TRIP = int(os.environ.get("PROXY_MAX_FAILURES_BEFORE_TRIP", "3"))
PROXY_COOLDOWN_SECONDS = int(os.environ.get("PROXY_COOLDOWN_SECONDS", "120"))  # circuit open cooldown
PROXY_EWMA_ALPHA = float(os.environ.get("PROXY_EWMA_ALPHA", "0.2"))
PROXY_REQUIRE_PROXY = os.environ.get("PROXY_REQUIRE_PROXY", "false").lower() in ("1","true","yes")
PROXY_FALLBACK_ALLOW_DIRECT = os.environ.get("PROXY_FALLBACK_ALLOW_DIRECT", "true").lower() in ("1","true","yes")

# Rate limiting config
RATE_LIMIT_PER_MINUTE = int(os.environ.get("RATE_LIMIT_PER_MINUTE", "30"))   # per-IP default
RATE_LIMIT_APIKEY = int(os.environ.get("RATE_LIMIT_APIKEY", "120"))         # per-API-key default
RATE_LIMIT_WINDOW_SEC = 60

# ---------- Engine circuit-breaker / attempts config (NEW) ----------
ENGINE_MAX_FAILURES = int(os.environ.get("ENGINE_MAX_FAILURES", "3"))           # fallos consecutivos antes de abrir circuito
ENGINE_COOLDOWN_SECONDS = int(os.environ.get("ENGINE_COOLDOWN_SECONDS", "120")) # cooldown tras abrir circuito
ENGINE_ATTEMPTS_PER_ENGINE = int(os.environ.get("ENGINE_ATTEMPTS_PER_ENGINE", "4"))  # intentos por motor antes de pasar al siguiente
ALLOW_SCRAPE_GOOGLE = os.environ.get("ALLOW_SCRAPE_GOOGLE", "false").lower() in ("1","true","yes")
# ------------------------------------------------------------------

# ---------- Politeness (por dominio) config (NEW) ----------
PER_DOMAIN_DELAY_BASE = float(os.environ.get("PER_DOMAIN_DELAY_BASE", "1.5"))   # segundos base entre requests al mismo host
PER_DOMAIN_DELAY_JITTER = float(os.environ.get("PER_DOMAIN_DELAY_JITTER", "0.8"))  # jitter +/- en segundos
PER_DOMAIN_CONCURRENCY = int(os.environ.get("PER_DOMAIN_CONCURRENCY", "1"))      # número simultáneo de requests por host
_DOMAIN_SEMAPHORE_ACQUIRE_TIMEOUT = float(os.environ.get("DOMAIN_SEMAPHORE_ACQUIRE_TIMEOUT", "30.0"))  # timeout al adquirir semáforo
# ------------------------------------------------------------------

# ---------------- Domain retry budget (reintentos por dominio) ----------------
DOMAIN_RETRY_BUDGET_DEFAULT = int(os.environ.get("DOMAIN_RETRY_BUDGET", "5"))  # reintentos por dominio antes de marcarlo
_domain_retry_lock = threading.Lock()
_domain_retry_budget: Dict[str, int] = {}  # map root_domain -> remaining retries

# ---------------- Backpressure / degraded-mode config ----------------
BACKPRESSURE_MAX_PENDING = int(os.environ.get("BACKPRESSURE_MAX_PENDING", str(max(100, MAX_WORKERS * 4))))
BACKPRESSURE_CHECK_RETRIES = int(os.environ.get("BACKPRESSURE_CHECK_RETRIES", "3"))
BACKPRESSURE_CHECK_SLEEP = float(os.environ.get("BACKPRESSURE_CHECK_SLEEP", "1.0"))  # segundos entre checks
DEGRADED_MAX_DOMAINS = int(os.environ.get("DEGRADED_MAX_DOMAINS", "40"))
DEGRADED_RELAX_QUALITY = int(os.environ.get("DEGRADED_RELAX_QUALITY", "15"))  # reduce quality target
DEGRADED_SEARCH_RESULTS_PER_QUERY = int(os.environ.get("DEGRADED_SEARCH_RESULTS_PER_QUERY", "20"))
DEGRADED_SHORT_HEAD_TIMEOUT = float(os.environ.get("DEGRADED_SHORT_HEAD_TIMEOUT", "1.5"))
DEGRADED_SHORT_GET_TIMEOUT = float(os.environ.get("DEGRADED_SHORT_GET_TIMEOUT", "2.0"))
DEGRADED_PREFERRED_ORDER = (os.environ.get("DEGRADED_PREFERRED_ORDER", "ddg,searx,gsearch").split(","))

# ---------------- Seen LRU config (mejora 13) ----------------
SEEN_MAX_SIZE = int(os.environ.get("SEEN_MAX_SIZE", "20000"))  # tamaño bounded para dedupe LRU

# logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")

# Flask app
app = Flask(__name__)

# ---------------- HTTP Session with pool & retries ----------------
SESSION = requests.Session()
RETRY_STRAT = Retry(total=2, backoff_factor=0.3, status_forcelist=(429, 500, 502, 503, 504))
ADAPTER = HTTPAdapter(pool_connections=HTTP_CONCURRENCY, pool_maxsize=HTTP_CONCURRENCY, max_retries=RETRY_STRAT)
SESSION.mount("https://", ADAPTER)
SESSION.mount("http://", ADAPTER)

def rand_headers(additional: dict = None) -> dict:
    h = HEADERS_BASE.copy()
    h["User-Agent"] = random.choice(USER_AGENTS)
    if additional:
        h.update(additional)
    return h

# ---------------- ReDoS-safe regex helpers ----------------
@functools.lru_cache(maxsize=_SAFE_RE_COMPILE_CACHE_SIZE)
def _compile_re_cached(pattern_str: str, flags: int = 0):
    # Compila y cachea patrones por string+flags
    return re.compile(pattern_str, flags)

def _ensure_compiled(pattern, flags=0):
    """
    Acepta str o Pattern. Si es str -> usa cache; si ya es Pattern -> lo devuelve.
    """
    try:
        if hasattr(pattern, "search"):
            return pattern
    except Exception:
        pass
    return _compile_re_cached(pattern, flags)

def _safe_truncate_for_regex(s: Optional[str], max_len: Optional[int] = None) -> str:
    if not s:
        return ""
    max_len = SAFE_REGEX_MAX_INPUT if max_len is None else int(max_len)
    s = str(s)
    if len(s) > max_len:
        return s[:max_len]
    return s

def safe_findall(pattern, text, flags=0, max_len: Optional[int] = None):
    try:
        txt = _safe_truncate_for_regex(text, max_len)
        cre = _ensure_compiled(pattern, flags)
        return cre.findall(txt)
    except Exception:
        return []

def safe_search(pattern, text, flags=0, max_len: Optional[int] = None):
    try:
        txt = _safe_truncate_for_regex(text, max_len)
        cre = _ensure_compiled(pattern, flags)
        return cre.search(txt)
    except Exception:
        return None

def safe_match(pattern, text, flags=0, max_len: Optional[int] = None):
    try:
        txt = _safe_truncate_for_regex(text, max_len)
        cre = _ensure_compiled(pattern, flags)
        return cre.match(txt)
    except Exception:
        return None

# ---------------- LRUSet + canonicalization helpers (Mejora 13) ----------------
class LRUSet:
    """
    Set con comportamiento LRU bounded. Implementado con OrderedDict para eficiencia.
    - add(item) -> True si fue añadido (no estaba), False si ya existía.
    - __contains__(item) -> bool
    - len(), iteración, clear()
    """
    def __init__(self, maxsize: int = 10000):
        self._maxsize = max(1, int(maxsize))
        self._od = collections.OrderedDict()

    def add(self, item) -> bool:
        if item in self._od:
            try:
                self._od.move_to_end(item)
            except Exception:
                pass
            return False
        self._od[item] = True
        while len(self._od) > self._maxsize:
            try:
                self._od.popitem(last=False)
            except Exception:
                break
        return True

    def __contains__(self, item) -> bool:
        return item in self._od

    def __len__(self) -> int:
        return len(self._od)

    def clear(self):
        self._od.clear()

    def items(self):
        return list(self._od.keys())

def _normalize_hostname(host: str) -> str:
    """
    Normaliza host:
      - strip
      - quitar trailing dot
      - lowercase
      - punycode (idna) si está disponible
      - no gestiona el puerto aquí
    """
    if not host:
        return ""
    h = host.strip().rstrip(".")
    try:
        h = h.lower()
    except Exception:
        pass
    # si contiene IPv6 con brackets, dejarlo
    if h.startswith("[") and h.endswith("]"):
        return h
    # no tocar puerto aquí; separarlo con urlparse si viene
    try:
        if idna:
            try:
                # si incluye caracteres no-ascii esto convertirá a punycode
                h = idna.encode(h).decode("ascii")
            except Exception:
                # si falla, mantener la versión lowercase
                pass
    except Exception:
        pass
    return h

def canonicalize_netloc(parsed: urlparse) -> Tuple[str, Optional[int], str]:
    """
    Devuelve (host_canonical, port_or_None, scheme)
    """
    host = parsed.hostname or ""
    port = parsed.port
    scheme = (parsed.scheme or "").lower()
    host = _normalize_hostname(host)
    # quitar puerto por defecto
    try:
        if port:
            if (scheme == "http" and port == 80) or (scheme == "https" and port == 443):
                port = None
    except Exception:
        pass
    return host, port, scheme

def canonical_domain_key_from_url(url: str, prefer_root: bool = True) -> str:
    """
    Toma una URL o cadena, la parsea y devuelve la clave canónica para dedupe.
    Por política del proyecto devolvemos root_domain_of(host) (ej: example.com) si prefer_root True.
    Si prefer_root False devuelve host punycode normalizado (ej: blog.example.com).
    """
    if not url:
        return ""
    try:
        u = url.strip()
        # for parsing, guarantee a scheme
        if not re.match(r"^[a-zA-Z][a-zA-Z0-9+\-.]*://", u):
            u = "https://" + u
        parsed = urlparse(u)
        host, port, scheme = canonicalize_netloc(parsed)
        if not host:
            return ""
        if prefer_root:
            try:
                root = root_domain_of(host)
                return root.lower()
            except Exception:
                return host.lower()
        return host.lower()
    except Exception:
        try:
            # fallback: strip schema and path
            return re.sub(r"^https?://", "", (url or "").strip(), flags=re.I).split("/")[0].lower()
        except Exception:
            return (url or "").strip().lower()

# ---------------- Proxy pool (robusto) ----------------
_proxy_lock = threading.Lock()
_PROXY_POOL: List[Dict[str, Any]] = []
_proxy_index = 0

def _normalize_proxy_string(s: str) -> str:
    s = s.strip()
    if not s:
        return ""
    if not s.startswith("http://") and not s.startswith("https://"):
        return "http://" + s
    return s

def load_proxies():
    global _PROXY_POOL
    proxies = []
    if PROXY_LIST_FILE and os.path.exists(PROXY_LIST_FILE):
        try:
            with open(PROXY_LIST_FILE, "r", encoding="utf-8") as f:
                for ln in f:
                    p = ln.strip()
                    if p:
                        proxies.append(p)
        except Exception as e:
            logging.debug("Failed to read proxy file: %s", e)
    if PROXY_LIST_STR:
        for p in PROXY_LIST_STR.split(","):
            p = p.strip()
            if p:
                proxies.append(p)
    normalized = []
    for p in proxies:
        if not p:
            continue
        n = _normalize_proxy_string(p)
        normalized.append(n)
    with _proxy_lock:
        new_pool = []
        for p in normalized:
            new_pool.append({
                "url": p,
                "healthy": True,
                "last_checked": 0.0,
                "failures": 0,
                "successes": 0,
                "avg_latency": 0.0,
                "circuit_open_until": 0.0,
                "last_error": ""
            })
        _PROXY_POOL = new_pool
    logging.info("Loaded %d proxies", len(_PROXY_POOL))

def _mark_proxy_success(pdict: Dict[str, Any], latency: float):
    with _proxy_lock:
        pdict["successes"] = pdict.get("successes", 0) + 1
        prev = pdict.get("avg_latency", 0.0)
        alpha = PROXY_EWMA_ALPHA
        pdict["avg_latency"] = (alpha * latency) + (1 - alpha) * prev if prev > 0 else latency
        pdict["failures"] = 0
        pdict["healthy"] = True
        pdict["last_checked"] = time.time()
        pdict["last_error"] = ""

def _mark_proxy_failure(pdict: Dict[str, Any], err: str):
    with _proxy_lock:
        pdict["failures"] = pdict.get("failures", 0) + 1
        pdict["last_checked"] = time.time()
        pdict["last_error"] = err[:200]
        if pdict["failures"] >= PROXY_MAX_FAILURES_BEFORE_TRIP:
            pdict["circuit_open_until"] = time.time() + PROXY_COOLDOWN_SECONDS
            pdict["healthy"] = False
            logging.info("Proxy %s tripped circuit (failures=%d) until %d", pdict["url"], pdict["failures"], pdict["circuit_open_until"])
        else:
            pdict["healthy"] = False

def _is_proxy_available(pdict: Dict[str, Any]) -> bool:
    now = time.time()
    if pdict.get("circuit_open_until", 0.0) > now:
        return False
    return bool(pdict.get("healthy", False))

def _health_check_proxy(pdict: Dict[str, Any]):
    url = PROXY_HEALTH_TEST_URL
    proxies = {"http": pdict["url"], "https": pdict["url"]}
    start = time.time()
    try:
        r = SESSION.request("get", url, timeout=4, allow_redirects=True, proxies=proxies)
        latency = time.time() - start
        status = r.status_code
        try:
            r.close()
        except Exception:
            pass
        if 200 <= status < 400:
            _mark_proxy_success(pdict, latency)
            return True
        else:
            _mark_proxy_failure(pdict, f"status:{status}")
            return False
    except Exception as e:
        _mark_proxy_failure(pdict, repr(e))
        return False

def _run_proxy_health_checks_once():
    with _proxy_lock:
        pool_snapshot = list(_PROXY_POOL)
    random.shuffle(pool_snapshot)
    for pdict in pool_snapshot:
        try:
            now = time.time()
            if pdict.get("circuit_open_until", 0.0) > now:
                continue
            _health_check_proxy(pdict)
            time.sleep(0.05)
        except Exception as e:
            logging.debug("health check error for proxy %s: %s", pdict.get("url"), e)
            continue

def _proxy_health_daemon():
    logging.info("Starting proxy health daemon (interval=%ds)", PROXY_HEALTH_CHECK_INTERVAL)
    while True:
        try:
            _run_proxy_health_checks_once()
        except Exception as e:
            logging.debug("Proxy health daemon error: %s", e)
        time.sleep(PROXY_HEALTH_CHECK_INTERVAL)

def start_proxy_health_thread():
    t = threading.Thread(target=_proxy_health_daemon, name="proxy-health", daemon=True)
    t.start()

def pick_proxy() -> Optional[str]:
    global _proxy_index
    with _proxy_lock:
        if not _PROXY_POOL:
            return None if PROXY_FALLBACK_ALLOW_DIRECT else "__NO_PROXY_AVAILABLE__"
        now = time.time()
        candidates = []
        for p in _PROXY_POOL:
            if p.get("circuit_open_until", 0.0) > now:
                continue
            if p.get("healthy", False):
                candidates.append(p)
        if not candidates:
            candidates_probe = [p for p in _PROXY_POOL if p.get("circuit_open_until", 0.0) <= now]
            if candidates_probe:
                p = random.choice(candidates_probe) if PROXY_ROTATION_MODE != "roundrobin" else candidates_probe[_proxy_index % len(candidates_probe)]
                _proxy_index = (_proxy_index + 1) % max(1, len(candidates_probe))
                return p["url"]
            if PROXY_REQUIRE_PROXY:
                return "__NO_PROXY_AVAILABLE__"
            return None if PROXY_FALLBACK_ALLOW_DIRECT else "__NO_PROXY_AVAILABLE__"
        if PROXY_ROTATION_MODE == "roundrobin":
            idx = _proxy_index % len(candidates)
            _proxy_index = (_proxy_index + 1) % len(candidates)
            return candidates[idx]["url"]
        elif PROXY_ROTATION_MODE == "latency":
            sorted_by_lat = sorted(candidates, key=lambda x: x.get("avg_latency") or 9999)
            return sorted_by_lat[0]["url"]
        else:
            return random.choice(candidates)["url"]

def get_proxy_status() -> List[Dict[str, Any]]:
    with _proxy_lock:
        return [dict(
            url=p["url"],
            healthy=bool(p.get("healthy", False)),
            failures=int(p.get("failures", 0)),
            successes=int(p.get("successes", 0)),
            avg_latency=float(p.get("avg_latency", 0.0)),
            circuit_open_until=float(p.get("circuit_open_until", 0.0)),
            last_checked=float(p.get("last_checked", 0.0)),
            last_error=str(p.get("last_error", ""))[:200]
        ) for p in _PROXY_POOL]

# initialize proxies and health thread
load_proxies()
start_proxy_health_thread()

# ---------------- SSRF / egress safety ----------------
@functools.lru_cache(maxsize=1024)
def is_private_host(host: str) -> bool:
    """
    Resuelve host y devuelve True si alguna IP de la resolución es privada/loopback/reserved/multicast.
    Si ocurre cualquier error en la resolución, devuelve True (conservador).
    Nota: NO se usa caché para forzar resolución en red.
    """
    try:
        if not host:
            return True
        if host.startswith("[") and host.endswith("]"):
            host = host[1:-1]
        try:
            ipobj = ipaddress.ip_address(host)
            if ipobj.is_private or ipobj.is_loopback or ipobj.is_reserved or ipobj.is_multicast:
                return True
            return False
        except Exception:
            pass
        for res in socket.getaddrinfo(host, None):
            ip = res[4][0]
            try:
                ipobj = ipaddress.ip_address(ip)
                if ipobj.is_private or ipobj.is_loopback or ipobj.is_reserved or ipobj.is_multicast:
                    return True
            except Exception:
                return True
        return False
    except Exception as e:
        logging.debug("is_private_host resolution failed for %s: %s", host, e)
        return True

# ---------------- Robots.txt (NO CACHE per user request) ----------------
def _fetch_robots_for_host(host: str) -> Optional[robotparser.RobotFileParser]:
    try:
        if not host:
            return None
        if is_private_host(host):
            logging.info("Not fetching robots.txt for private/reserved host: %s", host)
            return None
        parser = robotparser.RobotFileParser()
        candidates = [f"https://{host}/robots.txt", f"http://{host}/robots.txt"]
        content = None
        for url in candidates:
            try:
                r = SESSION.request("get", url, headers=rand_headers(), timeout=4, allow_redirects=True, proxies=None)
                if r and r.status_code == 200 and r.text:
                    content = r.text
                    try:
                        r.close()
                    except Exception:
                        pass
                    break
                if r:
                    try:
                        r.close()
                    except Exception:
                        pass
            except Exception as e:
                logging.debug("robots fetch error for %s: %s", url, e)
                continue
        if content is None:
            parser.parse("")  # empty => allows everything by default
            return parser
        lines = [ln.rstrip("\n") for ln in content.splitlines()]
        try:
            parser.parse(lines)
        except Exception:
            try:
                parser = robotparser.RobotFileParser()
                parser.parse(lines)
            except Exception:
                return None
        return parser
    except Exception as e:
        logging.debug("Failed to fetch/parse robots for %s: %s", host, e)
        return None

def is_allowed_by_robots(url: str, user_agent: Optional[str] = None) -> bool:
    try:
        parsed = urlparse(url)
        host = parsed.hostname or ""
        path = parsed.path or "/"
        if not host:
            return False
        host_l = host.lower()
        for bh in ROBOTS_BYPASS_HOSTS:
            if host_l == bh or host_l.endswith("." + bh):
                return True
        parser = _fetch_robots_for_host(host)
        if parser is None:
            return True
        ua = (user_agent or rand_headers().get("User-Agent") or "*")
        try:
            allowed = parser.can_fetch(ua, path)
            if not allowed:
                logging.info("Blocked by robots.txt: host=%s path=%s ua=%s", host, path, ua)
            return allowed
        except Exception:
            return True
    except Exception as e:
        logging.debug("is_allowed_by_robots error for %s: %s", url, e)
        return True

# ---------------- Politeness helpers (por dominio) ----------------
_domain_lock = threading.Lock()
_domain_last_request_ts: Dict[str, float] = {}
_domain_semaphores: Dict[str, threading.BoundedSemaphore] = {}

def _get_domain_semaphore(host: str) -> threading.BoundedSemaphore:
    with _domain_lock:
        sem = _domain_semaphores.get(host)
        if sem is None:
            sem = threading.BoundedSemaphore(PER_DOMAIN_CONCURRENCY)
            _domain_semaphores[host] = sem
        return sem

def _wait_for_domain_politeness(host: str):
    now = time.time()
    with _domain_lock:
        last = _domain_last_request_ts.get(host, 0.0)
    delay = PER_DOMAIN_DELAY_BASE + random.uniform(-PER_DOMAIN_DELAY_JITTER, PER_DOMAIN_DELAY_JITTER)
    to_wait = delay - (now - last)
    if to_wait > 0:
        logging.debug("Politeness: waiting %.2fs for host %s (delay target %.2fs, last=%.2f)", to_wait, host, delay, last)
        time.sleep(to_wait)

def _update_domain_last_ts(host: str):
    with _domain_lock:
        _domain_last_request_ts[host] = time.time()

# ---------------- Safe response wrapper ----------------
class _SafeResponse:
    """
    Response-like wrapper that contiene partes importantes de requests.Response
    pero garantiza que la respuesta original se cerró en http_request.
    """
    def __init__(self, status_code: int = None, text: str = "", content: bytes = b"", headers: dict = None, elapsed: timedelta = None, url: str = None):
        self.status_code = status_code
        self.text = text or ""
        self.content = content or b""
        self.headers = headers or {}
        self.elapsed = elapsed or timedelta(seconds=0)
        self.url = url

    def json(self):
        return json.loads(self.text) if self.text else {}

    def close(self):
        # no-op; original connection ya cerrada dentro de http_request
        return None

    def __bool__(self):
        return self.status_code is not None

# ---------------- http_request wrapper (con SSRF check + proxy pool + circuit handling + politeness) ----------------
def http_request(method: str, url: str, timeout: int = DEFAULT_TIMEOUT, allow_redirects: bool = True,
                 headers: dict = None, max_retries: int = 3, backoff_base: float = 2.0,
                 ignore_robots: bool = False) -> Optional[_SafeResponse]:
    parsed = None
    try:
        parsed = urlparse(url)
        host = parsed.hostname
        if host:
            if is_private_host(host):
                logging.warning("Blocked request to private/reserved host: %s (url=%s)", host, url)
                return None
    except Exception as e:
        logging.debug("http_request failed to parse URL for SSRF check %s: %s", url, e)
        return None

    skip_robots = bool(ignore_robots)
    try:
        if not skip_robots and parsed and parsed.hostname:
            host_l = parsed.hostname.lower()
            for bh in ROBOTS_BYPASS_HOSTS:
                if host_l == bh or host_l.endswith("." + bh):
                    skip_robots = True
                    break
    except Exception:
        pass

    ua_for_check = None
    try:
        if not skip_robots:
            ua_for_check = (headers or {}).get("User-Agent")
            if not ua_for_check:
                ua_for_check = rand_headers().get("User-Agent")
            if not is_allowed_by_robots(url, user_agent=ua_for_check):
                logging.warning("Request blocked by robots.txt policy: %s", url)
                return None
    except Exception as e:
        logging.debug("robots check failed for %s: %s", url, e)
        pass

    attempt = 0
    last_exc = None
    tried_proxies = set()
    while attempt <= max_retries:
        attempt += 1
        proxy = pick_proxy()
        if proxy == "__NO_PROXY_AVAILABLE__":
            logging.warning("Proxy required but none available; blocking request to %s", url)
            return None
        proxies = None
        proxy_used = None
        if proxy:
            if proxy in tried_proxies:
                proxy = None
            else:
                proxies = {"http": proxy, "https": proxy}
                proxy_used = proxy

        domain_sem = None
        sem_acquired = False
        host_for_politeness = parsed.hostname if parsed else None
        start_time = time.time()
        try:
            if host_for_politeness:
                try:
                    domain_sem = _get_domain_semaphore(host_for_politeness)
                    sem_acquired = domain_sem.acquire(timeout=_DOMAIN_SEMAPHORE_ACQUIRE_TIMEOUT)
                    if not sem_acquired:
                        logging.warning("Timeout acquiring semaphore for host %s (will proceed without semaphore)", host_for_politeness)
                except Exception as e:
                    logging.debug("Failed to acquire domain semaphore for %s: %s", host_for_politeness, e)
                    sem_acquired = False

            if host_for_politeness:
                try:
                    _wait_for_domain_politeness(host_for_politeness)
                except Exception as e:
                    logging.debug("Politeness wait failed for %s: %s", host_for_politeness, e)

            try:
                h = rand_headers(headers or {})
                # perform request
                r = SESSION.request(method.upper(), url, headers=h, timeout=timeout, allow_redirects=allow_redirects, proxies=proxies)
                if r is None:
                    raise requests.exceptions.RequestException("No response")
                # capture metadata & content immediately and close original response to avoid leaks
                try:
                    status = r.status_code
                except Exception:
                    status = None
                try:
                    text = r.text if getattr(r, "text", None) is not None else ""
                except Exception:
                    try:
                        # fallback to content decode
                        text = r.content.decode("utf-8", errors="replace") if getattr(r, "content", None) else ""
                    except Exception:
                        text = ""
                try:
                    content = r.content if getattr(r, "content", None) is not None else b""
                except Exception:
                    content = b""
                try:
                    headers_resp = dict(r.headers) if getattr(r, "headers", None) else {}
                except Exception:
                    headers_resp = {}
                try:
                    elapsed = getattr(r, "elapsed", None) or timedelta(seconds=(time.time() - start_time))
                    if not isinstance(elapsed, timedelta):
                        elapsed = timedelta(seconds=float(elapsed) if elapsed else 0.0)
                except Exception:
                    elapsed = timedelta(seconds=(time.time() - start_time))
                try:
                    url_resp = getattr(r, "url", url)
                except Exception:
                    url_resp = url
                # close the original response to free sockets/resources
                try:
                    r.close()
                except Exception:
                    pass

                # handle certain status cases (429, 5xx) - create SafeResponse to inspect status
                if status == 429:
                    logging.info("429 on %s (proxy=%s) attempt=%d", url, proxy_used, attempt)
                    if proxy_used:
                        with _proxy_lock:
                            pinfo = next((p for p in _PROXY_POOL if p["url"] == proxy_used), None)
                        if pinfo:
                            _mark_proxy_failure(pinfo, "429")
                            tried_proxies.add(proxy_used)
                    wait = min(backoff_base ** attempt + random.random(), MAX_BACKOFF)
                    last_exc = requests.exceptions.RequestException("429")
                    time.sleep(wait)
                    continue
                if status is not None and 500 <= status < 600:
                    if proxy_used:
                        with _proxy_lock:
                            pinfo = next((p for p in _PROXY_POOL if p["url"] == proxy_used), None)
                        if pinfo:
                            _mark_proxy_failure(pinfo, f"5xx:{status}")
                            tried_proxies.add(proxy_used)
                    wait = min(backoff_base ** attempt + random.random(), MAX_BACKOFF)
                    logging.info("5xx on %s status=%s (proxy=%s); retrying in %.1f s", url, status, proxy_used, wait)
                    last_exc = requests.exceptions.RequestException(f"5xx:{status}")
                    time.sleep(wait)
                    continue

                # on success or other statuses we return a SafeResponse built from captured data
                if proxy_used:
                    lat = elapsed.total_seconds() if elapsed else 0.0
                    with _proxy_lock:
                        pinfo = next((p for p in _PROXY_POOL if p["url"] == proxy_used), None)
                    if pinfo:
                        _mark_proxy_success(pinfo, lat)
                try:
                    if host_for_politeness:
                        _update_domain_last_ts(host_for_politeness)
                except Exception:
                    pass
                return _SafeResponse(status_code=status, text=text, content=content, headers=headers_resp, elapsed=elapsed, url=url_resp)

            except requests.exceptions.RequestException as e:
                last_exc = e
                logging.debug("Request exception for %s (proxy=%s): %s - retrying", url, proxy_used, e)
                if proxy_used:
                    with _proxy_lock:
                        pinfo = next((p for p in _PROXY_POOL if p["url"] == proxy_used), None)
                    if pinfo:
                        _mark_proxy_failure(pinfo, repr(e))
                        tried_proxies.add(proxy_used)
                wait = min(backoff_base ** attempt + random.random(), MAX_BACKOFF)
                time.sleep(wait)
                continue
            except Exception as e:
                last_exc = e
                logging.debug("Non-requests error for %s (proxy=%s): %s", url, proxy_used, e)
                if proxy_used:
                    with _proxy_lock:
                        pinfo = next((p for p in _PROXY_POOL if p["url"] == proxy_used), None)
                    if pinfo:
                        _mark_proxy_failure(pinfo, repr(e))
                        tried_proxies.add(proxy_used)
                time.sleep(min(backoff_base ** attempt, MAX_BACKOFF))
                continue
        finally:
            if sem_acquired and domain_sem:
                try:
                    if host_for_politeness:
                        _update_domain_last_ts(host_for_politeness)
                except Exception:
                    pass
                try:
                    domain_sem.release()
                except Exception:
                    logging.debug("Failed to release domain semaphore for %s", host_for_politeness)
    logging.debug("http_request failed for %s after %d attempts; last_exc=%s", url, max_retries, last_exc)
    return None

# ---------------- TF-IDF helper (safe regex use) ----------------
def tfidf_similarity(a: str, b: str) -> float:
    a = (a or "").strip()
    b = (b or "").strip()
    if not a or not b:
        return 0.0
    if _TFIDF_OK:
        try:
            vec = TfidfVectorizer(ngram_range=(1,2), max_features=4000).fit([a, b])
            m = vec.transform([a, b])
            A = m.toarray()[0]
            B = m.toarray()[1]
            num = float((A * B).sum())
            denom = (float((A*A).sum())**0.5) * (float((B*B).sum())**0.5) + 1e-9
            return float(num / denom) if denom > 0 else 0.0
        except Exception:
            logging.debug("TFIDF failed, falling back to token overlap")
    sa = set(safe_findall(r"[A-Za-zÀ-ÿ0-9]{3,}", a.lower()))
    sb = set(safe_findall(r"[A-Za-zÀ-ÿ0-9]{3,}", b.lower()))
    if not sa or not sb:
        return 0.0
    inter = sa.intersection(sb)
    return len(inter) / max(len(sa), len(sb))

# ---------------- Concurrency primitives ----------------
_http_semaphore = threading.BoundedSemaphore(HTTP_CONCURRENCY)
_executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS)

# ---------------- Fast filter (Capa 0) ----------------
_suspicious_tlds = { "xyz", "top", "club", "online", "pw", "tk", "loan", "win" }
_fast_blacklist_patterns = [
    r"(cheap|free[- ]?download|get[- ]?paid|captcha|proxy|clickbait|earn money|make money|work from home|millionaire)\b",
    r"(viagra|casino|porn|adult|sex)\b",
]
_fast_blacklist_re = [re.compile(p, re.I) for p in _fast_blacklist_patterns]

def root_domain_of(domain: str) -> str:
    if not domain:
        return ""
    try:
        if tldextract:
            ext = tldextract.extract(domain)
            if ext.domain:
                return f"{ext.domain}.{ext.suffix}" if ext.suffix else ext.domain
        parts = domain.split(".")
        if len(parts) >= 2:
            return ".".join(parts[-2:])
        return domain
    except Exception:
        return domain

_dynamic_blacklist: Dict[str, int] = {}
def load_blacklist():
    global _dynamic_blacklist
    try:
        if os.path.exists(BLACKLIST_FILE):
            with open(BLACKLIST_FILE, "r", encoding="utf-8") as f:
                _dynamic_blacklist = json.load(f)
                logging.info("Loaded dynamic blacklist (%d entries)", len(_dynamic_blacklist))
    except Exception:
        _dynamic_blacklist = {}
def save_blacklist():
    try:
        with open(BLACKLIST_FILE, "w", encoding="utf-8") as f:
            json.dump(_dynamic_blacklist, f)
    except Exception:
        pass

def domain_mark_rejected(domain: str):
    """
    Marca un dominio (usando clave canónica root) como rechazado en el blacklist dinámico.
    """
    try:
        root = canonical_domain_key_from_url(domain, prefer_root=True) or root_domain_of(domain)
    except Exception:
        root = root_domain_of(domain)
    if not root:
        return
    cnt = _dynamic_blacklist.get(root, 0) + 1
    _dynamic_blacklist[root] = cnt
    logging.info("Marked %s as rejected count=%d", root, cnt)
    save_blacklist()

def domain_is_dynamic_blacklisted(domain: str) -> bool:
    try:
        root = canonical_domain_key_from_url(domain, prefer_root=True) or root_domain_of(domain)
    except Exception:
        root = root_domain_of(domain)
    return _dynamic_blacklist.get(root, 0) >= BLACKLIST_MIN_REJECTS

load_blacklist()

# ---------------- Domain retry budget helpers ----------------
def _root_key(domain: str) -> str:
    try:
        return canonical_domain_key_from_url(domain, prefer_root=True) or root_domain_of(domain)
    except Exception:
        return root_domain_of(domain)

def _get_domain_retry_budget(domain: str) -> int:
    root = _root_key(domain)
    with _domain_retry_lock:
        return _domain_retry_budget.get(root, DOMAIN_RETRY_BUDGET_DEFAULT)

def _ensure_domain_budget(domain: str):
    root = _root_key(domain)
    with _domain_retry_lock:
        if root not in _domain_retry_budget:
            _domain_retry_budget[root] = DOMAIN_RETRY_BUDGET_DEFAULT

def _decrement_domain_retry_budget(domain: str) -> int:
    root = _root_key(domain)
    with _domain_retry_lock:
        cur = _domain_retry_budget.get(root, DOMAIN_RETRY_BUDGET_DEFAULT)
        cur = max(0, cur - 1)
        _domain_retry_budget[root] = cur
    if cur <= 0:
        try:
            domain_mark_rejected(root)
        except Exception:
            logging.debug("Failed to mark rejected for %s", root)
        logging.info("Domain retry budget exhausted for %s -> marked rejected", root)
    else:
        logging.debug("Domain retry budget for %s decremented to %d", root, cur)
    return cur

def fast_filter(prompt: str, domain: str, keywords: Optional[List[str]] = None) -> Tuple[int, List[str], str]:
    score = 50
    reasons: List[str] = []
    d = domain.lower().strip()
    parts = d.split(".")
    tld = parts[-1] if len(parts) > 1 else ""
    if any(d.endswith(s) for s in SOCIAL_BLACKLIST):
        reasons.append("Social domain")
        score -= 80
        verdict = "reject"
        return max(0, score), reasons, verdict
    if tld in _suspicious_tlds:
        reasons.append(f"Suspicious TLD .{tld}")
        score -= 20
    if domain_is_dynamic_blacklisted(domain):
        reasons.append("Dynamic blacklist hit")
        score -= 40
    try:
        domain_tokens = set(safe_findall(r"[A-Za-z0-9]{3,}", d))
        prompt_tokens = set()
        if keywords:
            for k in keywords:
                prompt_tokens.update(safe_findall(r"[A-Za-z0-9]{3,}", k.lower()))
        else:
            prompt_tokens.update(safe_findall(r"[A-Za-z0-9]{3,}", (prompt or "").lower()))
        overlap = domain_tokens.intersection(prompt_tokens)
        overlap_score = min(len(overlap) * 6, 30)
        if overlap:
            reasons.append(f"Token overlap: {', '.join(list(overlap)[:6])}")
            score += overlap_score
    except Exception:
        pass
    for rr in _fast_blacklist_re:
        try:
            if (safe_search(rr, domain) is not None) or (safe_search(rr, prompt) is not None):
                reasons.append("Detected spammy pattern")
                score -= 40
                break
        except Exception:
            continue
    root = root_domain_of(domain)
    if root in TRUSTED_WHITELIST or domain in TRUSTED_WHITELIST:
        reasons.append("Trusted whitelist")
        score += 40
    score = max(0, min(100, int(score)))
    if score >= FAST_ACCEPT_THRESHOLD:
        verdict = "accept"
    elif score <= FAST_REJECT_THRESHOLD:
        verdict = "reject"
    else:
        verdict = "maybe"
    return int(score), reasons, verdict

# ---------------- Helper to safely extract URLs from arbitrary backend items ----------------
def safe_extract_urls(item, _depth=0, _max_depth=6, _acc=None, _max_urls=200) -> List[str]:
    """
    Extracción segura de URLs desde estructuras arbitrarias.
    - limita profundidad (_max_depth)
    - limita número total de URLs devueltas por item (_max_urls)
    - evita aplicar operaciones costosas sobre strings muy grandes
    """
    if _acc is None:
        _acc = []
    try:
        if _depth > _max_depth:
            return []
        if item is None:
            return []
        # strings: aceptamos si parecen urls (pero truncamos primero)
        if isinstance(item, str):
            s = item.strip()
            if s:
                _acc.append(s)
            return list(dict.fromkeys(_acc))[:_max_urls]
        # dict: mira claves habituales y luego valores
        if isinstance(item, dict):
            for k in ("href", "url", "link", "result", "link_url"):
                if len(_acc) >= _max_urls:
                    break
                v = item.get(k)
                if v and isinstance(v, str):
                    _acc.append(v.strip())
            if len(_acc) < _max_urls:
                for v in item.values():
                    if len(_acc) >= _max_urls:
                        break
                    if isinstance(v, str) and v.startswith("http"):
                        _acc.append(v.strip())
            return list(dict.fromkeys(_acc))[:_max_urls]
        # list/tuple/set: iterar con límite de profundidad/urls
        if isinstance(item, (tuple, list, set)):
            for sub in item:
                if len(_acc) >= _max_urls:
                    break
                try:
                    safe_extract_urls(sub, _depth=_depth+1, _max_depth=_max_depth, _acc=_acc, _max_urls=_max_urls)
                except Exception:
                    continue
            return list(dict.fromkeys(u for u in _acc if u))[:_max_urls]
        # iterables genéricos
        try:
            for sub in item:
                if len(_acc) >= _max_urls:
                    break
                safe_extract_urls(sub, _depth=_depth+1, _max_depth=_max_depth, _acc=_acc, _max_urls=_max_urls)
            return list(dict.fromkeys(u for u in _acc if u))[:_max_urls]
        except Exception:
            pass
    except Exception:
        pass
    return list(dict.fromkeys(u for u in _acc if u))[:_max_urls]

# ---------------- Network-level helpers ----------------
def domain_alive(domain: str, head_timeout=HEAD_TIMEOUT, get_timeout=DEFAULT_TIMEOUT, retries=2) -> bool:
    if not domain:
        return False
    schemes = ("https://", "http://")
    for scheme in schemes:
        url = scheme + domain + "/"
        attempt = 0
        while attempt <= retries:
            attempt += 1
            try:
                with _http_semaphore:
                    r = http_request("head", url, timeout=head_timeout, allow_redirects=True, max_retries=1)
                if r is not None and r.status_code < 400:
                    try:
                        r.close()
                    except Exception:
                        pass
                    return True
                if r is not None and r.status_code in (403, 405, 400):
                    with _http_semaphore:
                        r2 = http_request("get", url, timeout=get_timeout, allow_redirects=True, max_retries=1)
                    if r2 is not None and r2.status_code < 400:
                        try:
                            r2.close()
                        except Exception:
                            pass
                        return True
                if r is not None:
                    try:
                        r.close()
                    except Exception:
                        pass
            except Exception:
                time.sleep(0.5 + random.random() * 0.5)
            time.sleep(0.1)
    return False

def domain_alive_short(domain: str) -> bool:
    try:
        return domain_alive(domain, head_timeout=int(DEGRADED_SHORT_HEAD_TIMEOUT), get_timeout=int(DEGRADED_SHORT_GET_TIMEOUT), retries=0)
    except Exception:
        return False

def sanitize_url_candidate(u: str) -> Optional[str]:
    try:
        if not u or not isinstance(u, str):
            return None
        u = u.strip()
        parsed = urlparse(u)
        if parsed.scheme and parsed.scheme not in ("http", "https"):
            return None
        if not parsed.netloc:
            # usar safe_match para evitar ReDoS
            if safe_match(r"^[A-Za-z0-9\.-]+\.[A-Za-z]{2,6}(/|$)", u):
                return "https://" + u
            return None
        path = parsed.path or "/"
        return u if parsed.scheme else f"https://{parsed.netloc}{path}"
    except Exception:
        return None

def clean_domain_from_url(url: str) -> str:
    try:
        u = url.strip()
        if u.startswith("/url?q="):
            u = u.split("/url?q=", 1)[1].split("&")[0]
        p = urlparse(u if safe_match(r"^https?://", u, flags=re.I) else ("https://" + u))
        net = p.netloc or p.path
        net = net.split("/")[0].split(":")[0]
        net = re.sub(r"^www\.", "", net, flags=re.I)
        return net.lower()
    except Exception:
        return ""

# ---------------- Fetch + heavy_check improvements ----------------
def fetch_homepage_text(domain: str, timeout: int = 6) -> str:
    try:
        with _http_semaphore:
            url = f"https://{domain}/"
            r = http_request("get", url, timeout=timeout, allow_redirects=True)
            if not r or r.status_code != 200:
                if r:
                    try:
                        r.close()
                    except Exception:
                        pass
                url = f"http://{domain}/"
                r = http_request("get", url, timeout=timeout, allow_redirects=True)
            if r and r.status_code == 200 and r.text:
                text = r.text
                try:
                    r.close()
                except Exception:
                    pass
                soup = BeautifulSoup(text, "html.parser")
                texts = []
                title = ""
                try:
                    title = soup.title.string.strip() if soup.title and soup.title.string else ""
                except Exception:
                    title = ""
                if title:
                    texts.append(title)
                m = None
                try:
                    m = soup.find("meta", attrs={"name": "description"})
                except Exception:
                    m = None
                if m and m.get("content"):
                    texts.append(m.get("content").strip())
                ps = [p.get_text(" ", strip=True) for p in soup.find_all("p")][:8]
                texts.extend([p for p in ps if p])
                if not texts:
                    texts.append(soup.get_text(" ", strip=True)[:4000])
                return " ".join(texts)[:20000]
            if r:
                try:
                    r.close()
                except Exception:
                    pass
    except Exception as e:
        logging.debug("fetch_homepage_text error %s: %s", domain, e)
    return ""

# ---------------- whois seguro (async + timeout) ----------------
_whois_executor = concurrent.futures.ThreadPoolExecutor(max_workers=2)

def _whois_lookup(domain: str):
    try:
        return whois_lib.whois(domain)
    except Exception as e:
        logging.debug("whois lookup failed for %s: %s", domain, e)
        return None

def get_domain_age_months(domain: str) -> Optional[int]:
    if not whois_lib:
        return None
    try:
        fut = _whois_executor.submit(_whois_lookup, domain)
        try:
            info = fut.result(timeout=4.0)
        except concurrent.futures.TimeoutError:
            try:
                fut.cancel()
            except Exception:
                pass
            logging.debug("whois timed out for %s", domain)
            return None
        if not info:
            return None
        cd = info.get("creation_date") if isinstance(info, dict) else getattr(info, "creation_date", None)
        if not cd:
            return None
        if isinstance(cd, list):
            cd = cd[0]
        if not hasattr(cd, "year"):
            return None
        years = time.gmtime().tm_year - cd.year
        months = years * 12 + max(0, getattr(cd, "month", 1) - 1)
        return int(months)
    except Exception as e:
        logging.debug("get_domain_age_months error %s: %s", domain, e)
        return None

def assess_domain_quality(domain: str) -> Tuple[int, List[str]]:
    score = 50
    reasons: List[str] = []
    try:
        r = http_request("get", f"https://{domain}/", timeout=6, allow_redirects=True)
        if r and r.status_code == 200:
            text = r.text
            try:
                r.close()
            except Exception:
                pass
            score = 65
            reasons = ["Reachable homepage (200)"]
            try:
                soup = BeautifulSoup(text, "html.parser")
                p_count = len(soup.find_all("p"))
                if p_count >= 5:
                    reasons.append(f"Content paragraphs={p_count}")
                    score = min(100, score + 8)
                author_meta = soup.find("meta", attrs={"name": _ensure_compiled(r"author", re.I)})
                if author_meta and author_meta.get("content"):
                    reasons.append("Meta author found")
                    score = min(100, score + 6)
                if soup.find(attrs={"itemtype": _ensure_compiled(r"schema.org", re.I)}) or soup.find("script", type="application/ld+json"):
                    reasons.append("Structured data found")
                    score = min(100, score + 6)
            except Exception:
                pass
        else:
            sc = r.status_code if r else "no-response"
            if r:
                try:
                    r.close()
                except Exception:
                    pass
            score = 35
            reasons = [f"HTTP status {sc}"]
    except Exception as e:
        logging.debug("assess_domain_quality error %s: %s", domain, e)
        score = 20
        reasons = ["No reachable homepage"]
    age_months = get_domain_age_months(domain)
    if age_months is not None:
        if age_months >= 60:
            reasons.append(f"Domain age {age_months} months (old)")
            score = min(100, score + 12)
        elif age_months >= 12:
            reasons.append(f"Domain age {age_months} months")
            score = min(100, score + 6)
    if score >= QUALITY_ACCEPT:
        reasons.insert(0, f"Score: {score} (aceptable)")
    else:
        reasons.insert(0, f"Score: {score} (rechazado)")
    return int(score), reasons

def heavy_check(prompt: str, domain: str, keywords: Optional[List[str]]=None) -> Dict:
    reasons: List[str] = []
    score = 50
    try:
        q_score, q_reasons = assess_domain_quality(domain)
        reasons.extend(q_reasons[:6])
        score = max(score, q_score)
    except Exception as e:
        logging.debug("heavy_check assess failed: %s", e)
    text = ""
    try:
        text = fetch_homepage_text(domain, timeout=8)
        if text:
            sim = tfidf_similarity(prompt, text)
            reasons.append(f"TFIDF-sim={sim:.3f}")
            score = min(100, int(score + sim * 45))
            if len(text) > 2000:
                reasons.append("Long content (>2000 chars)")
                score = min(100, score + 6)
        else:
            reasons.append("No homepage text fetched")
    except Exception as e:
        logging.debug("heavy_check fetch_homepage_text failed: %s", e)
        reasons.append("Error fetching homepage text")
    try:
        with _http_semaphore:
            r = http_request("get", f"https://{domain}/", timeout=6, allow_redirects=True)
        if r and r.status_code == 200:
            text2 = r.text
            try:
                r.close()
            except Exception:
                pass
            soup = BeautifulSoup(text2, "html.parser")
            title = ""
            try:
                title = soup.title.string.strip() if soup.title and soup.title.string else ""
            except Exception:
                title = ""
            h1 = ""
            try:
                h1_tag = soup.find("h1")
                if h1_tag:
                    h1 = h1_tag.get_text(" ", strip=True)
            except Exception:
                h1 = ""
            for candidate in (title, h1):
                if candidate and prompt.lower() in candidate.lower():
                    reasons.append("Prompt in title/h1")
                    score = min(100, score + 10)
                    break
    except Exception:
        pass
    try:
        age_months = get_domain_age_months(domain)
        if age_months and age_months >= 24:
            reasons.append(f"Domain age bonus ({age_months} months)")
            score = min(100, score + 4)
    except Exception:
        pass
    score = max(0, min(100, int(score)))
    verdict = "accept" if score >= QUALITY_ACCEPT else ("reject" if score < QUALITY_WARN else "maybe")
    return {"score": int(score), "reasons": reasons, "verdict": verdict}

# ---------------- Prompt analysis (keywords + intent) ----------------
def simple_keyword_extraction(text: str, top_n: int = 6) -> List[str]:
    text = (text or "").strip()
    if not text:
        return []
    if _nlp:
        try:
            doc = _nlp(text)
            candidates = []
            for chunk in doc.noun_chunks:
                tok = chunk.text.strip().lower()
                if len(tok) > 2:
                    candidates.append(tok)
            freq = {}
            for c in candidates:
                freq[c] = freq.get(c, 0) + 1
            sorted_k = sorted(freq.items(), key=lambda x: x[1], reverse=True)
            kws = [k for k, _ in sorted_k][:top_n]
            if kws:
                return kws
        except Exception:
            pass
    tokens = safe_findall(r"[A-Za-zÀ-ÿ0-9\-_]{3,}", text.lower())
    stopwords = set(("que","para","con","como","la","el","de","y","en","los","las","del","un","una","por","al","se","su"))
    freq = {}
    for t in tokens:
        if t in stopwords or t.isdigit() or len(t) < 3:
            continue
        freq[t] = freq.get(t, 0) + 1
    sorted_items = sorted(freq.items(), key=lambda x: x[1], reverse=True)
    kws = [k for k, _ in sorted_items][:top_n]
    return kws

def rule_based_intent(text: str) -> str:
    t = text.lower()
    trans_k = ("comprar", "precio", "contratar", "oferta", "venta", "cotización", "cotizar", "presupuesto")
    info_k = ("qué", "como", "cómo", "qué es", "información", "guía", "tutorial", "explica")
    nav_k = ("sitio", "web", "url", "ir a", "entrar", "homepage")
    local_k = ("cerca", "cerca de", "en madrid", "en barcelona", "en españa")
    if any(w in t for w in trans_k):
        return "transactional"
    if any(w in t for w in info_k):
        return "informational"
    if any(w in t for w in nav_k):
        return "navigational"
    if any(w in t for w in local_k):
        return "local"
    return "informational"

def analyze_prompt(prompt: str) -> Dict[str, Any]:
    prompt = (prompt or "").strip()
    if not prompt:
        return {"summary": "", "keywords": [], "intent": None, "entities": [], "country_hint": None}
    keywords = simple_keyword_extraction(prompt, top_n=8)
    intent = rule_based_intent(prompt)
    summary = " ".join(prompt.split()[:40])
    logging.info("Prompt analysis -> intent=%s keywords=%s summary=%s", intent, keywords, (summary[:140] + ("..." if len(summary) > 140 else "")))
    return {"summary": summary, "keywords": keywords, "intent": intent, "entities": [], "country_hint": None}

# ---------------- Query builder (NO geo injection) ----------------
def build_social_exclusion() -> str:
    toks = []
    for d in sorted(SOCIAL_BLACKLIST):
        toks.append(f"-site:{d}")
    return " ".join(toks)

def prompt_to_queries(prompt: str, variants: int = 3, site_filters="site:.es OR site:.com",
                      lang="es", country: Optional[str]=None, keywords: Optional[List[str]] = None,
                      intent: Optional[str] = None) -> List[str]:
    p = (prompt or "").strip()
    if not p:
        return []
    parts = [pp.strip() for pp in re.split(r"[\r\n;]+", p) if pp.strip()]
    templates = [
        '{part} "{kws}" {site} lang:{lang} {exclusions}',
        '{part} {site} "{kws}" lang:{lang} {exclusions}',
        '"{kws}" {part} {site} {exclusions}'
    ]
    if keywords and isinstance(keywords, list) and keywords:
        kws = " ".join(keywords[:6])
    else:
        tokens = safe_findall(r"[A-Za-zÀ-ÿ0-9\-]{3,}", p)
        kws = " ".join(tokens[:6]) if tokens else p

    if intent:
        if intent == "transactional":
            kws = f"{kws} comprar precio oferta"
        elif intent == "local":
            kws = f"{kws} cerca de 'cerca de' ubicación"

    exclusions = build_social_exclusion()
    site = site_filters or ""
    queries = []
    for part in parts:
        for i in range(variants):
            tpl = templates[i % len(templates)]
            q = tpl.format(part=part, kws=kws, site=site, lang=lang, exclusions=exclusions).strip()
            q = re.sub(r"\s+", " ", q)
            if q not in queries:
                queries.append(q)
    return queries

# ---------------- Search backends (robust) ----------------
def search_gsearch(query: str, max_results: int = 20, country: Optional[str]=None) -> List[str]:
    if not _GSEARCH_OK or gsearch_func is None:
        return []
    try:
        results = gsearch_func(query, num_results=max_results, lang="es")
        if isinstance(results, (list, tuple)):
            return [r for r in results if isinstance(r, str)][:max_results]
        else:
            return list(results)[:max_results]
    except Exception as e:
        logging.debug("gsearch error: %s", e)
        return []

def search_ddg(query: str, max_results: int = 20, country: Optional[str]=None) -> List[str]:
    if not _DDG_OK or _DDGS_CLASS is None:
        return []
    try:
        ddg = _DDGS_CLASS()
        try:
            items = list(ddg.text(query, region="es", safesearch="Off", timelimit=None))
        except TypeError:
            items = list(ddg.text(query))
        urls = []
        for it in items:
            urls.extend(safe_extract_urls(it))
        cleaned = []
        for u in urls:
            if not isinstance(u, str):
                continue
            if u.startswith("/url?q="):
                u = u.split("/url?q=", 1)[1].split("&")[0]
            cleaned.append(u)
        return cleaned[:max_results]
    except Exception as e:
        logging.debug("[ddg] error: %s", e)
        return []

def search_searx(query: str, max_results: int = 20, country: Optional[str]=None) -> List[str]:
    urls = []
    for inst in SEARX_INSTANCES:
        try:
            q = quote_plus(query)
            extra = "&language=es" if country and country.upper() == "ES" else ""
            url = f"{inst.rstrip('/')}/search?q={q}&format=json&categories=general{extra}"
            r = http_request("get", url, timeout=DEFAULT_TIMEOUT, allow_redirects=True, ignore_robots=True)
            if not r:
                continue
            try:
                j = r.json()
            except Exception:
                try:
                    r.close()
                except Exception:
                    pass
                continue
            try:
                r.close()
            except Exception:
                pass
            for item in j.get("results", [])[:max_results]:
                urls.extend(safe_extract_urls(item))
            if urls:
                break
        except Exception as e:
            logging.debug("[searx] instance failed %s -> %s", inst, e)
            continue
    return urls[:max_results]

def fallback_scrape_google(query: str, max_results: int = 10, country: Optional[str]=None) -> List[str]:
    if not ALLOW_SCRAPE_GOOGLE:
        logging.info("Scrape Google skipped (ALLOW_SCRAPE_GOOGLE is false)")
        return []
    try:
        q = quote_plus(query)
        host = "www.google.com"
        url = f"https://{host}/search?q={q}&num={max_results}&hl=es"
        if not is_allowed_by_robots(url):
            logging.info("Google scrape blocked by robots.txt (skipping).")
            return []
        r = http_request("get", url, timeout=DEFAULT_TIMEOUT, allow_redirects=True, ignore_robots=False)
        if not r:
            return []
        text = r.text
        try:
            r.close()
        except Exception:
            pass
        soup = BeautifulSoup(text, "html.parser")
        urls = []
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if href.startswith("/url?q="):
                u = href.split("/url?q=")[1].split("&")[0]
                urls.append(u)
            elif href.startswith("http"):
                urls.append(href)
        return urls[:max_results]
    except Exception as e:
        logging.debug("[scrape-google] error: %s", e)
        return []

# ---------------- Unified search-with-fallback (Google-first + circuit-breaker) ----------------
_allowed = {"gsearch": search_gsearch, "ddg": search_ddg, "searx": search_searx, "scrape": fallback_scrape_google}

_engine_lock = threading.Lock()
_ENGINE_STATUS: Dict[str, Dict[str, Any]] = {}
for en in _allowed.keys():
    _ENGINE_STATUS[en] = {"failures": 0, "successes": 0, "last_failure": 0.0, "circuit_open_until": 0.0, "last_error": ""}

def engine_is_available(engine: str) -> bool:
    st = _ENGINE_STATUS.get(engine)
    if not st:
        return False
    now = time.time()
    if st.get("circuit_open_until", 0.0) > now:
        return False
    return True

def engine_mark_failure(engine: str, err: str = ""):
    with _engine_lock:
        st = _ENGINE_STATUS.setdefault(engine, {"failures": 0, "successes": 0, "last_failure": 0.0, "circuit_open_until": 0.0, "last_error": ""})
        st["failures"] = st.get("failures", 0) + 1
        st["last_failure"] = time.time()
        st["last_error"] = (err or "")[:300]
        logging.info("Engine %s failure count=%d err=%s", engine, st["failures"], st["last_error"])
        if st["failures"] >= ENGINE_MAX_FAILURES:
            st["circuit_open_until"] = time.time() + ENGINE_COOLDOWN_SECONDS
            logging.warning("Engine %s tripped circuit until %d (failures=%d)", engine, int(st["circuit_open_until"]), st["failures"])

def engine_mark_success(engine: str):
    with _engine_lock:
        st = _ENGINE_STATUS.setdefault(engine, {"failures": 0, "successes": 0, "last_failure": 0.0, "circuit_open_until": 0.0, "last_error": ""})
        st["successes"] = st.get("successes", 0) + 1
        st["failures"] = 0
        st["last_error"] = ""
        st["circuit_open_until"] = 0.0
        logging.debug("Engine %s marked success (successes=%d)", engine, st["successes"])

@app.route("/engine_status", methods=["GET"])
def engine_status_view():
    with _engine_lock:
        status = {k: dict(v) for k, v in _ENGINE_STATUS.items()}
    return jsonify({"engines": status})

def search_with_fallback(query: str, max_results: int = 20, country: Optional[str]=None,
                         preferred_order: Optional[List[str]] = None) -> List[str]:
    if preferred_order is None:
        preferred_order = ["gsearch", "ddg", "searx", "scrape"]

    active_order = []
    for en in preferred_order:
        if en == "scrape" and not ALLOW_SCRAPE_GOOGLE:
            logging.debug("Skipping 'scrape' engine because ALLOW_SCRAPE_GOOGLE is false")
            continue
        active_order.append(en)

    for engine in active_order:
        fn = _allowed.get(engine)
        if not fn:
            logging.debug("Engine %s not available", engine)
            continue
        if not engine_is_available(engine):
            logging.info("Engine %s is in cooldown; skipping", engine)
            continue

        attempt = 0
        last_err = ""
        while attempt < ENGINE_ATTEMPTS_PER_ENGINE:
            attempt += 1
            try:
                urls = retry_with_backoff(fn, query, max_results=max_results, retries=2, backoff_base=1.8, country=country)
                if not isinstance(urls, (list, tuple)):
                    try:
                        urls = list(urls)
                    except Exception:
                        urls = [urls] if urls else []
                flat_urls = []
                for it in urls:
                    flat_urls.extend(safe_extract_urls(it))
                flat_urls = [u for u in flat_urls if u]
                logging.info("Engine %s attempt %d returned %d flat urls", engine, attempt, len(flat_urls))
                if flat_urls:
                    engine_mark_success(engine)
                    return flat_urls[:max_results]
                else:
                    last_err = "empty-results"
                    engine_mark_failure(engine, "empty-results")
                    if not engine_is_available(engine):
                        logging.warning("Engine %s entered cooldown after empty results", engine)
                        break
                    time.sleep(min(0.5 * attempt + random.random() * 0.5, 4.0))
                    continue
            except Exception as e:
                last_err = repr(e)
                logging.debug("Engine %s attempt %d raised exception: %s", engine, attempt, e)
                engine_mark_failure(engine, last_err)
                if not engine_is_available(engine):
                    logging.warning("Engine %s entered cooldown after exception", engine)
                    break
                time.sleep(min(1.0 * attempt + random.random(), 6.0))
                continue
        logging.info("Engine %s exhausted %d attempts without usable results (last_err=%s)", engine, ENGINE_ATTEMPTS_PER_ENGINE, last_err)
    logging.info("All engines exhausted for query (no results)")
    return []

# ---------------- Backpressure helpers & degraded pipeline ----------------
def _executor_pending_size() -> int:
    try:
        q = getattr(_executor, "_work_queue", None)
        if q is None:
            return 0
        return int(q.qsize())
    except Exception:
        return 0

def is_overloaded() -> bool:
    try:
        pending = _executor_pending_size()
        if pending >= BACKPRESSURE_MAX_PENDING:
            logging.debug("Backpressure check: pending=%d threshold=%d -> overloaded", pending, BACKPRESSURE_MAX_PENDING)
            return True
        return False
    except Exception:
        return False

def quick_degraded_pipeline(queries: List[str], desired: int, prompt: str, keywords: Optional[List[str]], intent: Optional[str], validate: bool) -> List[Dict]:
    domains: List[Dict] = []
    seen = LRUSet(SEEN_MAX_SIZE)
    deg_target = min(desired, DEGRADED_MAX_DOMAINS)
    preferred = [p for p in DEGRADED_PREFERRED_ORDER if p in _allowed]
    if not preferred:
        preferred = ["ddg", "searx", "gsearch"]
    for q in queries:
        try:
            urls = []
            try:
                urls = retry_with_backoff(search_with_fallback, q, max_results=DEGRADED_SEARCH_RESULTS_PER_QUERY, retries=1, backoff_base=1.4, country=None, preferred_order=preferred)
                if not isinstance(urls, (list, tuple)):
                    try:
                        urls = list(urls)
                    except Exception:
                        urls = [urls] if urls else []
            except Exception:
                urls = []
            for u in urls:
                if len(domains) >= deg_target:
                    return domains
                try:
                    cand = sanitize_url_candidate(u) or u
                    key = canonical_domain_key_from_url(cand, prefer_root=True)
                    if not key or key in seen:
                        continue
                    dom = clean_domain_from_url(cand) or key
                    # normalizar dom a la representación display (root)
                    dom = key
                    if any(dom.endswith(s) for s in SOCIAL_BLACKLIST):
                        continue
                    if domain_is_dynamic_blacklisted(dom):
                        continue
                    budget = _get_domain_retry_budget(dom)
                    if budget <= 0:
                        try:
                            domain_mark_rejected(dom)
                        except Exception:
                            pass
                        continue
                    score, reasons, verdict = fast_filter(prompt, dom, keywords)
                    relaxed_threshold = max(20, QUALITY_TARGET - DEGRADED_RELAX_QUALITY)
                    if verdict == "accept" and score >= relaxed_threshold:
                        seen.add(key)
                        domains.append({"domain": dom, "quality": score, "reasons": reasons + [f"degraded:fast:{score}"], "source_engine": "degraded"})
                        continue
                    if validate:
                        try:
                            if domain_alive_short(dom):
                                seen.add(key)
                                domains.append({"domain": dom, "quality": max(20, score), "reasons": reasons + ["degraded:short-head"], "source_engine": "degraded"})
                                continue
                        except Exception:
                            pass
                except Exception:
                    continue
            time.sleep(0.05)
        except Exception:
            continue
    return domains

# ---------------- Rate limiter (simple fixed window) ----------------
_rate_lock = threading.Lock()
_rate_table: Dict[str, Dict[str, Any]] = {}

def get_client_ip(flask_request) -> str:
    xff = flask_request.headers.get("X-Forwarded-For", "")
    if xff:
        ip = xff.split(",")[0].strip()
        return ip
    return flask_request.remote_addr or "unknown"

def allow_request(client_id: str, limit: int) -> Tuple[bool, int]:
    now = time.time()
    with _rate_lock:
        rec = _rate_table.get(client_id)
        if rec is None:
            _rate_table[client_id] = {"count": 1, "window_start": now}
            return True, limit - 1
        window_start = rec.get("window_start", now)
        if now - window_start >= RATE_LIMIT_WINDOW_SEC:
            rec["count"] = 1
            rec["window_start"] = now
            _rate_table[client_id] = rec
            return True, limit - 1
        else:
            if rec["count"] >= limit:
                return False, 0
            rec["count"] += 1
            remaining = max(0, limit - rec["count"])
            _rate_table[client_id] = rec
            return True, remaining

# ---------------- Orchestrator: get_domains_from_prompt ----------------
def get_domains_from_prompt(prompt: str,
                            per_engine: int = 20,
                            max_domains: int = 80,
                            engines: Optional[List[str]] = None,
                            validate: bool = True,
                            country: Optional[str] = None,
                            keywords: Optional[List[str]] = None,
                            intent: Optional[str] = None) -> List[Dict]:
    engines_order = ["gsearch", "ddg", "searx", "scrape"]

    site_filters = "site:.es OR site:.com"
    queries = prompt_to_queries(prompt, variants=3, site_filters=site_filters, lang="es", country=None, keywords=keywords, intent=intent)
    if not queries:
        return []

    desired = int(max_domains)
    domains: List[Dict] = []
    seen = LRUSet(SEEN_MAX_SIZE)
    maybe_candidates: Dict[str, Dict] = {}
    logging.info("Starting domain search: desired=%d QUALITY_TARGET=%d", desired, QUALITY_TARGET)

    cycle = 0
    local_per_engine = per_engine
    fallback_thresholds = list(range(QUALITY_TARGET, QUALITY_ACCEPT - 1, -5))

    while len(domains) < desired and cycle < MAX_CYCLES:
        cycle += 1
        remaining = desired - len(domains)
        fetch_per_engine = min(int(local_per_engine * OVERSHOOT_FACTOR), 300)
        logging.info("Cycle %d - need %d more (fetch_per_engine=%d)", cycle, remaining, fetch_per_engine)

        candidate_urls = []
        for qi, q in enumerate(queries, start=1):
            logging.debug("Query [%d/%d]: %s", qi, len(queries), q)
            time.sleep(random.uniform(*JITTER_BETWEEN_QUERIES))
            try:
                urls = retry_with_backoff(search_with_fallback, q, max_results=fetch_per_engine, retries=2, backoff_base=1.8, country=None, preferred_order=engines_order)
                if not isinstance(urls, (list, tuple)):
                    try:
                        urls = list(urls)
                    except Exception:
                        urls = [urls] if urls else []
                flat_urls = []
                for it in urls:
                    flat_urls.extend(safe_extract_urls(it))
                urls = flat_urls
            except Exception as e:
                logging.debug("Unified search failed for query %s: %s", q, e)
                urls = []
            logging.debug(" -> unified search returned %d urls", len(urls))
            if urls:
                candidate_urls.extend([(u, "unified") for u in urls])

        random.shuffle(candidate_urls)
        logging.info("Collected candidate_urls count=%d", len(candidate_urls))

        if is_overloaded():
            logging.warning("Backpressure detected (pending >= %d). Will perform short re-checks before degrading.", BACKPRESSURE_MAX_PENDING)
            recheck_ok = False
            for attempt in range(BACKPRESSURE_CHECK_RETRIES):
                time.sleep(BACKPRESSURE_CHECK_SLEEP * (1 + random.random() * 0.5))
                if not is_overloaded():
                    recheck_ok = True
                    logging.info("Backpressure cleared on re-check %d", attempt + 1)
                    break
                logging.info("Backpressure still present on re-check %d/%d", attempt + 1, BACKPRESSURE_CHECK_RETRIES)
            if not recheck_ok:
                logging.warning("Switching to degraded pipeline after %d failed re-checks", BACKPRESSURE_CHECK_RETRIES)
                deg_domains = quick_degraded_pipeline(queries, remaining, prompt, keywords, intent, validate)
                for item in deg_domains:
                    key = canonical_domain_key_from_url(item.get("domain", ""), prefer_root=True) or item.get("domain")
                    if key not in seen:
                        seen.add(key)
                        domains.append(item)
                logging.info("Degraded pipeline returned %d domains (requested remaining=%d)", len(deg_domains), remaining)
                final = domains[:desired]
                if len(final) < desired:
                    logging.warning("Degraded: could not reach requested count (%d) - returning %d", desired, len(final))
                return final

        futures = {}
        accepted_this_cycle = []

        for (u, src) in candidate_urls:
            if len(domains) + len(accepted_this_cycle) >= desired:
                break
            try:
                cand = sanitize_url_candidate(u) or u
                key = canonical_domain_key_from_url(cand, prefer_root=True)
                if not key or key in seen:
                    continue
                dom = key  # canonical root representation used throughout
                if any(dom.endswith(s) for s in SOCIAL_BLACKLIST):
                    continue
                if domain_is_dynamic_blacklisted(dom):
                    continue
                if validate:
                    try:
                        if not domain_alive(dom):
                            domain_mark_rejected(dom)
                            continue
                    except Exception:
                        continue
                root = dom
                if root in TRUSTED_WHITELIST or dom in TRUSTED_WHITELIST:
                    seen.add(key)
                    accepted_this_cycle.append({"domain": dom, "quality": 100, "reasons": ["Whitelisted"], "source_engine": src})
                    time.sleep(random.uniform(*JITTER_BETWEEN_PAGES))
                    continue
                score, reasons, verdict = fast_filter(prompt, dom, keywords)
                logging.debug("fast_filter %s -> %s (%d) %s", dom, verdict, score, (reasons[:2] if reasons else []))
                if verdict == "accept" and score >= QUALITY_TARGET:
                    seen.add(key)
                    accepted_this_cycle.append({"domain": dom, "quality": score, "reasons": reasons + [f"fast:{score}"], "source_engine": src})
                    continue
                if verdict == "reject":
                    domain_mark_rejected(dom)
                    continue
                if dom not in futures and dom not in maybe_candidates:
                    budget = _get_domain_retry_budget(dom)
                    if budget <= 0:
                        logging.debug("Skipping domain %s due to exhausted retry budget", dom)
                        try:
                            domain_mark_rejected(dom)
                        except Exception:
                            pass
                        continue
                    _ensure_domain_budget(dom)
                    future = _executor.submit(heavy_check, prompt, dom, keywords)
                    futures[future] = (dom, src)
            except Exception as e:
                logging.debug("candidate processing error: %s", e)
                continue

        for future, (dom, src) in list(futures.items()):
            try:
                res = future.result(timeout=HEAVY_TIMEOUT_SECS)
                verdict = res.get("verdict")
                score = int(res.get("score", 0))
                reasons = res.get("reasons", [])
                if score >= QUALITY_TARGET:
                    key = canonical_domain_key_from_url(dom, prefer_root=True) or dom
                    if key not in seen:
                        seen.add(key)
                        accepted_this_cycle.append({"domain": dom, "quality": score, "reasons": reasons + [f"heavy:{score}"], "source_engine": src})
                        logging.info(" + heavy accepted %s (score=%d)", dom, score)
                else:
                    maybe_candidates[dom] = {"domain": dom, "quality": score, "reasons": reasons + [f"heavy:{score}"], "source_engine": src}
                time.sleep(random.uniform(*JITTER_BETWEEN_PAGES))
            except concurrent.futures.TimeoutError:
                logging.info("heavy_check timeout for %s", dom)
                try:
                    future.cancel()
                except Exception:
                    pass
                try:
                    _decrement_domain_retry_budget(dom)
                except Exception:
                    logging.debug("Failed to decrement retry budget for %s after timeout", dom)
            except Exception as e:
                logging.debug("heavy_check error for %s: %s", dom, e)
                try:
                    _decrement_domain_retry_budget(dom)
                except Exception:
                    logging.debug("Failed to decrement retry budget for %s after exception", dom)

        accepted_this_cycle_sorted = sorted(accepted_this_cycle, key=lambda x: x.get("quality", 0), reverse=True)
        for item in accepted_this_cycle_sorted:
            if len(domains) >= desired:
                break
            domains.append(item)

        logging.info("Cycle %d done: accepted so far = %d / %d", cycle, len(domains), desired)
        if len(domains) < desired:
            local_per_engine = min(local_per_engine + 10, 1000)
            logging.info("Not enough accepted; increasing per_engine to %d and continuing", local_per_engine)
            time.sleep(min(1 + cycle, 6))

    if len(domains) < desired and maybe_candidates:
        logging.info("Attempting fallback relaxation to fill requested domains (desired=%d current=%d)", desired, len(domains))
        sorted_maybe = sorted(maybe_candidates.values(), key=lambda x: x.get("quality", 0), reverse=True)
        for thr in fallback_thresholds:
            if len(domains) >= desired:
                break
            for cand in sorted_maybe:
                if len(domains) >= desired:
                    break
                key = canonical_domain_key_from_url(cand.get("domain", ""), prefer_root=True) or cand.get("domain")
                if cand["quality"] >= thr and key not in seen:
                    seen.add(key)
                    domains.append(cand)
            logging.info("After relaxing to %d -> total accepted = %d", thr, len(domains))

    if len(domains) < desired:
        logging.warning("Final fallback: not enough high-quality domains; filling with best available to reach %d results", desired)
        pool = {d["domain"]: d for d in list(maybe_candidates.values()) + domains}
        sorted_pool = sorted(pool.values(), key=lambda x: x.get("quality", 0), reverse=True)
        for item in sorted_pool:
            if len(domains) >= desired:
                break
            if item["domain"] in [d["domain"] for d in domains]:
                continue
            domains.append(item)

    final = domains[:desired]
    if len(final) < desired:
        logging.warning("Could not reach requested count (%d) - returning %d", desired, len(final))
    return final

# ---------------- Flask UI ----------------
TEMPLATE = """<!doctype html>
<html lang="es">
<head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Domain Finder (NLP prompt)</title>
<style>body{font-family:Inter,system-ui,Arial;background:#f6f8fb;color:#0f1724;padding:20px}.wrap{max-width:980px;margin:20px auto}.card{background:#fff;padding:16px;border-radius:10px;box-shadow:0 6px 18px rgba(15,23,42,0.06)}textarea{width:100%;min-height:120px;padding:10px;border-radius:8px;border:1px solid #e6e9ef}.controls{display:flex;gap:12px;flex-wrap:wrap;margin-top:10px}button{background:#0ea5a4;color:#fff;padding:10px 14px;border:0;border-radius:8px;cursor:pointer}.results{margin-top:12px;background:#fff;padding:12px;border-radius:8px}.row{padding:6px 0;border-bottom:1px dashed #eee}.muted{color:#647486;font-size:14px}.score{float:right;font-weight:700}.notice{color:#a16207}.error{color:#b91c1c;font-weight:700}</style>
</head><body><main class="wrap"><h1>Domain Finder (prompt → dominios)</h1><div class="card"><form method="POST" action="/search"><label>Prompt / descripción</label><textarea name="prompt" required>{{ request.form.get('prompt','') }}</textarea><div class="controls"><label>Resultados por motor <input type="number" name="per_engine" value="{{ per_engine }}" min="1" max="1000"></label><label>Máx dominios <input type="number" name="max_domains" value="{{ max_domains }}" min="1" max="1000"></label><label><input type="checkbox" name="validate" {% if validate %}checked{% endif %}> Validar que dom responde</label></div><div style="margin-top:12px"><button type="submit">Buscar dominios</button></div></form></div>{% if error %}<div class="results"><div class="error">{{ error }}</div></div>{% endif %}{% if analysis %}<div class="results"><h3>Análisis del prompt</h3><div class="muted">Intent: {{ analysis.intent }}</div><div class="muted">Keywords: {{ analysis.keywords|join(', ') }}</div><div class="muted">Summary: {{ analysis.summary }}</div></div>{% endif %}{% if dominios %}<div class="results"><h3>Dominios encontrados ({{ dominios|length }})</h3>{% for d in dominios %}<div class="row"><strong>{{ d.domain }}</strong><span class="score">{{ d.quality }}</span><br><span class="muted">https://{{ d.domain }}</span>{% if d.reasons %}<div class="muted">Motivos: {{ d.reasons|join(' • ') }}</div>{% endif %}</div>{% endfor %}</div>{% endif %}<footer style="margin-top:12px;color:#647486">Respeta robots.txt y no uses los resultados para spam. Para escala usa proxies o APIs oficiales. <a href="/tos">TOS</a></footer></main></body></html>"""

@app.route("/", methods=["GET"])
def home():
    return render_template_string(TEMPLATE, dominios=None, error=None, per_engine=20, max_domains=10, validate=True, warnings=None, analysis=None)

@app.route("/health", methods=["GET"])
def health():
    return Response("ok", mimetype="text/plain")

@app.route("/proxy_status", methods=["GET"])
def proxy_status():
    status = get_proxy_status()
    return jsonify({"count": len(status), "proxies": status})

@app.route("/tos", methods=["GET"])
def tos():
    tos_html = """
    <!doctype html>
    <html lang="es">
    <head><meta charset="utf-8"><title>Términos de uso - Domain Finder</title></head>
    <body style="font-family:Arial,Helvetica,sans-serif;margin:30px;">
      <h2>Términos de uso (resumen)</h2>
      <p>Este servicio está diseñado para ayudar en búsquedas de dominios y análisis básicos. <strong>NO</strong> debe utilizarse para scraping agresivo, abuso o recolección masiva de datos personales.</p>
      <ul>
        <li>Respeta <code>robots.txt</code> de cada sitio. Nuestra aplicación intentará respetarlo automáticamente y bloqueará requests que estén expresamente prohibidas por <code>robots.txt</code>.</li>
        <li>No utilices los resultados para enviar spam, ataques o actividades que violen las políticas del sitio objetivo.</li>
        <li>Si necesitas escala o scraping intensivo, utiliza APIs oficiales o solicita permiso al propietario del sitio.</li>
      </ul>
      <p>Si tienes dudas legales o de cumplimiento, consulta con un experto en tu jurisdicción.</p>
      <p><a href="/">Volver</a></p>
    </body>
    </html>
    """
    return Response(tos_html, mimetype="text/html")

@app.route("/search", methods=["POST"])
def search_view():
    api_key = request.form.get("api_key") or request.headers.get("X-API-Key")
    if api_key:
        client_id = f"apikey:{api_key}"
        limit = RATE_LIMIT_APIKEY
    else:
        client_ip = get_client_ip(request)
        client_id = f"ip:{client_ip}"
        limit = RATE_LIMIT_PER_MINUTE

    allowed, remaining = allow_request(client_id, limit)
    if not allowed:
        logging.warning("Rate limit exceeded for %s (limit=%d)", client_id, limit)
        return Response("Too Many Requests", status=429, mimetype="text/plain")

    prompt_raw = request.form.get("prompt", "") or ""
    prompt = prompt_raw.strip()

    # --- NUEVAS REGLAS DE SEGURIDAD / SANITIZACIÓN DEL PROMPT ---
    truncated_notice = False
    # 1) Si el prompt excede PROMPT_MAX_CHARS lo recortamos (trim) para evitar cargas excesivas.
    if len(prompt) > PROMPT_MAX_CHARS:
        prompt = prompt[:PROMPT_MAX_CHARS]
        truncated_notice = True
        logging.info("Prompt trimmed from %d to %d chars", len(prompt_raw), PROMPT_MAX_CHARS)

    # 2) Si hay 'palabras' absurdamente largas (> PROMPT_MAX_WORD) rechazamos la petición.
    giant_word_match = safe_search(r"\S{" + str(PROMPT_MAX_WORD + 1) + r",}", prompt_raw, max_len=PROMPT_MAX_CHARS*2)
    if giant_word_match:
        msg = f"Se rechazó el prompt: contiene una palabra demasiado larga (> {PROMPT_MAX_WORD} caracteres)."
        logging.warning("Rejecting prompt due giant token length: %d+ chars", PROMPT_MAX_WORD)
        return render_template_string(TEMPLATE, dominios=None, error=msg, per_engine=20, max_domains=10, validate=True, warnings=None, analysis=None)

    if not prompt:
        return render_template_string(TEMPLATE, dominios=None, error="Introduce un prompt.", per_engine=20, max_domains=10, validate=True, warnings=None, analysis=None)

    try:
        per_engine = int(request.form.get("per_engine", 20))
        max_domains = int(request.form.get("max_domains", 10))
    except Exception:
        per_engine = 20
        max_domains = 10
    validate = bool(request.form.get("validate", "off") == "on")

    analysis = analyze_prompt(prompt)
    if truncated_notice:
        # añadir aviso de truncado en el summary para que el usuario lo vea en la UI
        analysis["summary"] = (analysis.get("summary", "") + f" [TRUNCATED TO {PROMPT_MAX_CHARS} chars]")
    keywords = analysis.get("keywords")
    intent = analysis.get("intent")

    try:
        dominios = get_domains_from_prompt(prompt, per_engine=per_engine, max_domains=max_domains,
                                           validate=validate, country=None, keywords=keywords, intent=intent)
    except Exception as e:
        logging.exception("Search failed")
        return render_template_string(TEMPLATE, dominios=None, error=f"Error en la búsqueda: {e}", per_engine=per_engine, max_domains=max_domains, validate=validate, warnings=None, analysis=analysis)

    if not dominios:
        return render_template_string(TEMPLATE, dominios=None, error="No se encontraron dominios. Prueba a afinar el prompt.", per_engine=per_engine, max_domains=max_domains, validate=validate, warnings=None, analysis=analysis)

    warnings = []
    for d in dominios:
        if d["quality"] < QUALITY_TARGET:
            warnings.append(f"Dominio {d['domain']} calidad baja (score={d['quality']})")
    resp = render_template_string(TEMPLATE, dominios=dominios, error=None, per_engine=per_engine, max_domains=max_domains, validate=validate, warnings=warnings, analysis=analysis)
    response = Response(resp, mimetype="text/html")
    response.headers["X-RateLimit-Remaining"] = str(remaining)
    return response

# ---------------- Entrypoint / helpers ----------------
def retry_with_backoff(fn, *args, retries=2, backoff_base=2.0, max_backoff=MAX_BACKOFF, **kwargs):
    attempt = 0
    backoff = backoff_base
    while True:
        attempt += 1
        try:
            return fn(*args, **kwargs)
        except requests.exceptions.RequestException as e:
            logging.debug("Request exception: %s", e)
            if attempt > retries:
                raise
            wait = min(backoff, max_backoff)
            logging.info("Transient error, retrying in %.1f s (attempt %d/%d)", wait, attempt, retries)
            time.sleep(wait)
            backoff *= backoff_base
        except Exception as e:
            logging.debug("Non-requests error: %s", e)
            if attempt > retries:
                raise
            wait = min(backoff, max_backoff)
            logging.info("Error, retrying in %.1f s (attempt %d/%d)", wait, attempt, retries)
            time.sleep(wait)
            backoff *= backoff_base

if __name__ == "__main__":
    logging.info("Starting Domain Finder (QUALITY_TARGET=%d) on port %d", QUALITY_TARGET, PORT)
    logging.info("Engine circuit-breaker config: ENGINE_MAX_FAILURES=%d ENGINE_COOLDOWN_SECONDS=%d ENGINE_ATTEMPTS_PER_ENGINE=%d ALLOW_SCRAPE_GOOGLE=%s",
                 ENGINE_MAX_FAILURES, ENGINE_COOLDOWN_SECONDS, ENGINE_ATTEMPTS_PER_ENGINE, ALLOW_SCRAPE_GOOGLE)
    logging.info("Politeness config: PER_DOMAIN_DELAY_BASE=%.2f PER_DOMAIN_DELAY_JITTER=%.2f PER_DOMAIN_CONCURRENCY=%d",
                 PER_DOMAIN_DELAY_BASE, PER_DOMAIN_DELAY_JITTER, PER_DOMAIN_CONCURRENCY)
    logging.info("Backpressure config: BACKPRESSURE_MAX_PENDING=%d BACKPRESSURE_CHECK_RETRIES=%d", BACKPRESSURE_MAX_PENDING, BACKPRESSURE_CHECK_RETRIES)
    app.run(host="0.0.0.0", port=PORT)
