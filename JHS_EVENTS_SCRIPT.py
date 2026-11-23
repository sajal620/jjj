import urllib.request
import json
import sys
import re
import random
import threading
from typing import Optional, List, Tuple
from urllib import request, parse
import os
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import urlparse, urlunparse, urlencode, parse_qs, unquote
import uuid
import time
import subprocess
from datetime import datetime, timezone, timedelta

# =========================
# TERMUX COLOR CODES
# =========================

BLACK   = "\033[30m"
RED     = "\033[91m"
GREEN   = "\033[92m"
YELLOW  = "\033[93m"
BLUE    = "\033[94m"
MAGENTA = "\033[95m"
CYAN    = "\033[96m"
WHITE   = "\033[97m"

DARK_RED     = "\033[31m"
DARK_GREEN   = "\033[32m"
DARK_YELLOW  = "\033[33m"
DARK_BLUE    = "\033[34m"
DARK_MAGENTA = "\033[35m"
DARK_CYAN    = "\033[36m"
GRAY         = "\033[90m"

BOLD_RED     = "\033[1;91m"
BOLD_GREEN   = "\033[1;92m"
BOLD_YELLOW  = "\033[1;93m"
BOLD_BLUE    = "\033[1;94m"
BOLD_MAGENTA = "\033[1;95m"
BOLD_CYAN    = "\033[1;96m"
BOLD_WHITE   = "\033[1;97m"

UNDERLINE = "\033[4m"
RESET = "\033[0m"

API_TEMPLATE = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug_path}/watch"

# =========================
# INDIA TIMEZONE (IST = UTC+5:30)
# =========================
IST = timezone(timedelta(hours=5, minutes=30))
_IST_OFFSET_SEC = 5 * 3600 + 30 * 60   # 19800 — added to UTC epoch for IST wall-clock

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

# token.txt — same folder as this script
TOKEN_FILE = os.path.join(_SCRIPT_DIR, "token.txt")

# Token directory:
#   1. FHD_TOKEN_DIR env var (if set)
#   2. <script_dir>/tokens/  (default)
TOKEN_DIR   = os.environ.get("FHD_TOKEN_DIR", os.path.join(_SCRIPT_DIR, "tokens"))
TOKEN_COUNT = 1044  # compatibility value; loader discovers every token*.txt present
# 4K streams use a separate token folder: <script_dir>/4K/
TOKEN_4K_DIR = os.environ.get("FHD_4K_TOKEN_DIR", os.path.join(_SCRIPT_DIR, "4K"))

# 24-hour cookie tokens (separate pool) — rotated, reused 5 hours
SD_TOKEN_DIR = os.environ.get(
    "SD_TOKEN_DIR",
    "/storage/emulated/0/Download/Cookies/SD",
)
COOKIE_24H_TTL_SEC = 15 * 3600  # reuse same 24h hdntl for 15 hours
_24H_COOKIE_CACHE = {"token": "", "fetched_at": 0.0, "tok_idx": 0}
_24H_DEFAULT_SLUG = "tv/star-sports-hindi-1/1260000025/live/watch"

# Auto-update settings
# - Tokens dir used ONLY to discover live events + fetch NEW stream links once
# - Existing M3U URLs are refreshed every cycle via CDN Set-Cookie (h.py style)
M3U_FILENAME   = "fhd_auto.m3u"
TOKEN_CYCLE    = 1    # minutes: rotate token slots independently of polling
LIVE_EVENT_INTERVAL_SEC = 60   # poll Hotstar and Sony live events every 60 seconds
M3U_REFRESH_INTERVAL_SEC = 70   # refresh existing M3U cookies every 70 seconds
EVENT_GRACE_MINUTES = 30  # remove event from M3U if gone from live API this long

# Global override for multi-token rotation in auto-update mode
_ACTIVE_TOKEN_OVERRIDE: Optional[str] = None

LANGUAGES = {
    "eng": "ENGLISH", "en": "ENGLISH",
    "hin": "HINDI",   "hi": "HINDI", "hd": "HINDI HD",
    "mar": "MARATHI", "mr": "MARATHI", "ma": "MARATHI",
    "guj": "GUJARATI","gu": "GUJARATI",
    "bho": "BHOJPURI","bh": "BHOJPURI","bih": "BHOJPURI",
    "pan": "PUNJABI", "pun": "PUNJABI","pa": "PUNJABI","pu": "PUNJABI",
    "har": "HARYANVI","hv": "HARYANVI","ha": "HARYANVI",
    "tam": "TAMIL",   "ta": "TAMIL",
    "tel": "TELUGU",  "te": "TELUGU",
    "kan": "KANNADA", "kn": "KANNADA",
    "mal": "MALAYALAM","ml": "MALAYALAM",
    "ben": "BENGALI", "bn": "BENGALI",
    "ori": "ORIYA",   "or": "ORIYA",
}

# ===================== UNIQUE_LANGUAGES =====================
_seen_lang_names = set()
_skip_lang_names = {"HINDI HD", "ORIYA"}
UNIQUE_LANGUAGES = {}
for _lc, _ln in LANGUAGES.items():
    if _ln in _skip_lang_names:
        continue
    if _ln not in _seen_lang_names:
        _seen_lang_names.add(_ln)
        UNIQUE_LANGUAGES[_lc] = _ln
del _seen_lang_names, _skip_lang_names, _lc, _ln

# ===================== LIVE EVENTS FETCHER CONSTANTS =====================
_LIVE_SLUGS_API = (
    "https://www.hotstar.com/api/internal/bff/v2/slugs"
    "/in/browse/editorial/live-now/1271392364"
)

_LIVE_CAPABILITIES = json.dumps({
    "ads": ["non_ssai"],
    "audio_channel": ["stereo"],
    "container": ["fmp4", "fmp4br", "ts"],
    "dvr": ["short"],
    "dynamic_range": ["sdr"],
    "encryption": ["plain"],
    "ladder": ["phone", "web"],
    "package": ["hls", "dash"],
    "resolution": ["sd", "hd", "fhd"],
    "video_codec": ["h264"],
    "video_codec_non_secure": ["h265", "h264"]
}, separators=(",", ":"))

_LIVE_DRM = json.dumps({
    "hdcp_version": ["HDCP_V2_2"],
    "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
}, separators=(",", ":"))

_SPORTS_SLUGS_API = (
    "https://www.hotstar.com/api/internal/bff/v2/slugs"
    "/in/browse/editorial/best-in-sports/6517"
)

# =========================
# PROXY CONFIG
# =========================
PROXY_IP   = ""
PROXY_PORT = 0
PROXY_URL  = ""  # disabled — direct only
# Aliases used by auto_update_mode (keeps names consistent with config refs)
LIVE_CF_CONFIG = CF_CONFIG_FILE = "livecf_config.json"
FHD_TOKEN_DIR = TOKEN_DIR
MAX_TOKENS    = TOKEN_COUNT
FHD_M3U_FILE  = M3U_FILENAME
CYCLE_MINUTES = TOKEN_CYCLE  # 1 min

# =========================
# HEADERS BASE
# =========================

HEADERS_BASE = {
    "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en",
    "Connection": "keep-alive",
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "same-origin",
    "x-hs-retry-count": "0",
    "X-HS-Platform": "androidtv",
    "X-Country-Code": "in",
    "X-HS-Accept-language": "eng",
    "x-hs-is-retry": "false",
    "X-HS-Client": "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690",
    "x-hs-app": "260510002",
    "Alt-Used": "www.hotstar.com",
    "Pragma": "no-cache",
    "Cache-Control": "no-cache",
}

HEADERS_BASE_4KADS = {
    "User-Agent": "Hotstar;in.startv.hotstar/26.03.30.2.11580 (Android/12)",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "eng",
    "Referer": "https://www.hotstar.com/in/explore?search_query=live",
    "Connection": "keep-alive",
    "X-HS-Platform": "androidtv",
    "X-Country-Code": "in",
    "X-HS-Accept-language": "eng",
    "x-hs-is-retry": "false",
    "x-hs-retry-count": "0",
    "X-HS-Client": "platform:androidtv;app_id:in.startv.hotstar;app_version:26.03.06.0;os:Android;os_version:12;schema_version:0.0.1690",
    "x-hs-app": "260306000",
    "Pragma": "no-cache",
    "Cache-Control": "no-cache",
}

# ===================== DEVICE POOL (5-HOUR COOLDOWN) =====================
import threading as _dev_threading

DEVICE_COOLDOWN_SEC = 5 * 3600  # 5 hours

_device_last_used: dict = {}
_device_lock = _dev_threading.Lock()

def _gen_random_app_version():
    year  = random.randint(24, 26)
    month = random.randint(1, 12)
    day   = random.randint(1, 28)
    build = random.randint(0, 9)
    ver   = f"{year}.{month:02d}.{day:02d}.{build}"
    code  = f"{year}{month:02d}{day:02d}{build:03d}"
    return ver, code

def _gen_random_os_version(platform: str) -> str:
    return str(random.randint(10, 15)) if platform == "androidtv" else str(random.randint(9, 15))

def _build_device_profile(platform: str, os_ver: str, app_ver: str, app_code: str) -> tuple:
    if platform == "androidtv":
        ua     = f"Hotstar;in.startv.hotstar.dplus.tv/{app_ver} (Android/{os_ver}; tv)"
        client = (f"platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
                  f"app_version:{app_ver};os:Android;os_version:{os_ver};schema_version:0.0.1690")
    else:
        ua     = f"Hotstar;in.startv.hotstar/{app_ver} (Android/{os_ver})"
        client = (f"platform:android;app_id:in.startv.hotstar;"
                  f"app_version:{app_ver};os:Android;os_version:{os_ver};schema_version:0.0.1690")
    return ua, client, app_code

def _get_device(platform: str) -> tuple:
    now = time.time()
    for _ in range(200):
        app_ver, app_code = _gen_random_app_version()
        os_ver = _gen_random_os_version(platform)
        key = (platform, os_ver, app_ver)
        with _device_lock:
            if now - _device_last_used.get(key, 0) >= DEVICE_COOLDOWN_SEC:
                _device_last_used[key] = now
                return _build_device_profile(platform, os_ver, app_ver, app_code)
    with _device_lock:
        if _device_last_used:
            oldest = min(_device_last_used, key=lambda k: _device_last_used[k])
            p, ov, av = oldest
            parts = av.split(".")
            ac = "".join(parts[:3]) + f"{int(parts[3]):03d}" if len(parts) == 4 else "260510002"
            _device_last_used[oldest] = now
            return _build_device_profile(p, ov, av, ac)
    return _build_device_profile(platform, "14", "26.05.10.2", "260510002")

def _get_atv_device() -> tuple:
    return _get_device("androidtv")

def _get_android_device() -> tuple:
    return _get_device("android")

# ===================== HEADER BUILDERS =====================

def build_headers() -> dict:
    ua, cs, app_code = _get_atv_device()
    headers = HEADERS_BASE.copy()
    headers["User-Agent"]       = ua
    headers["X-HS-Client"]      = cs
    headers["X-HS-Platform"]    = "androidtv"
    headers["x-hs-app"]         = app_code
    headers["X-Request-Id"]     = str(uuid.uuid4())
    headers["x-hs-request-id"]  = str(uuid.uuid4())
    headers["x-hs-device-id"]   = str(uuid.uuid4())
    headers["x-hs-usertoken"]   = load_user_token()
    return headers

def build_jhs_headers() -> dict:
    ua, cs, app_code = _get_atv_device()
    headers = HEADERS_BASE.copy()
    headers["User-Agent"]        = ua
    headers["X-HS-Client"]       = cs
    headers["X-HS-Platform"]     = "androidtv"
    headers["x-hs-app"]          = app_code
    headers["X-Request-Id"]      = str(uuid.uuid4())
    headers["x-hs-request-id"]   = str(uuid.uuid4())
    headers["x-hs-device-id"]    = str(uuid.uuid4())
    headers["x-hs-usertoken"]    = load_user_token()
    return headers

# ===================== TOKEN LOADING =====================

def load_user_token(token_path: str = TOKEN_FILE) -> str:
    global _ACTIVE_TOKEN_OVERRIDE
    if _ACTIVE_TOKEN_OVERRIDE is not None:
        return _ACTIVE_TOKEN_OVERRIDE
    try:
        with open(token_path, "r", encoding="utf-8") as token_file:
            return token_file.read().strip()
    except:
        return ""

def check_token_valid(token: str, slug_path: str = "sports/cricket") -> bool:
    try:
        test_url = f"https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug_path}/watch"
        _h = HEADERS_BASE.copy()
        _h["x-hs-usertoken"] = token
        _h["X-Request-Id"] = str(uuid.uuid4())
        _h["x-hs-request-id"] = str(uuid.uuid4())
        _h["x-hs-device-id"] = str(uuid.uuid4())
        req = request.Request(test_url, headers=_h)
        with request.urlopen(req, timeout=10) as resp:
            body = resp.read(4096)
        try:
            data = json.loads(body)
            if "success" not in data or not data.get("success"):
                return False
        except Exception:
            pass
        return True
    except Exception as _e:
        _code = getattr(_e, "code", None)
        if _code in (401, 403):
            return False
        return True

# ===================== URL HELPERS =====================

def extract_slug_path(url: str) -> Optional[str]:
    value = url.strip()
    parsed = parse.urlparse(value)
    path = parsed.path if parsed.scheme else value
    segments = [s for s in path.split("/") if s]
    if not segments:
        return None
    if segments[0] == "in":
        segments = segments[1:]
    if segments and segments[-1] == "watch":
        segments = segments[:-1]
    return "/".join(segments)

def extract_match_title(url: str) -> tuple:
    slug = extract_slug_path(url)
    if not slug:
        return "HOTSTAR CONTENT", ""
    parts = slug.split('/')
    match_no = ""
    match_search = re.search(r'(match[-_]?\d+|\bm\d+\b)', slug.lower())
    if match_search:
        match_no = match_search.group(1).replace('match', 'MATCH-').replace('m', 'MATCH-').upper()
        match_no = re.sub(r'-+', '-', match_no)
    for p in parts:
        if any(x in p for x in ["tata-ipl", "-vs-", "highlights", "replay"]):
            clean_name = p.replace('-highlights', '').replace('-replay', '').replace('-video', '')
            clean_name = re.sub(r'match[-_]?\d+|m\d+', '', clean_name)
            return clean_name.strip('-').replace('-', ' ').upper(), match_no
    name = parts[1] if len(parts) > 1 else parts[0]
    return name.replace('-', ' ').upper(), match_no

def extract_stream_type(url: str) -> str:
    u = url.lower()
    if "replay" in u:    return "REPLAY"
    if "highlights" in u: return "HIGHLIGHTS"
    if "clips" in u:     return "CLIP"
    if "/movies/" in u:  return "MOVIE"
    if "/sports/" in u and "/video/live/" in u: return "LIVE TV"
    if "/tv/" in u and "live" in u:             return "LIVE TV"
    if "/shows/" in u:   return "TV SHOW"
    return "STREAM"

def extract_hdntl_from_url(url: str) -> str:
    """Extract hdnea/hdntl from stream URL. Never cross the OTT '|' pipe boundary."""
    try:
        base = (url or "").split("|")[0].strip()
        parsed = urlparse(base)
        params = parse_qs(parsed.query)
        for key in ("hdnea", "hdntl"):
            if key in params and params[key]:
                tok = (params[key][0] or "").strip()
                # strip accidental pipe / cookie leakage
                tok = tok.split("|")[0].split("&")[0].strip()
                if tok.lower().startswith("hdntl="):
                    tok = tok[6:]
                if tok.lower().startswith("hdnea="):
                    tok = tok[6:]
                if "exp=" in tok:
                    return tok
        # pipe section: cookie=hdntl=TOKEN
        if "|" in (url or ""):
            m = re.search(r"(?:cookie=)?hdntl=([^&|;\s]+)", url.split("|", 1)[1], flags=re.I)
            if m and "exp=" in m.group(1):
                return m.group(1).strip()
    except Exception:
        pass
    return ""

# ===================== STREAM EXTRACTION =====================

def extract_best_stream(player_config: dict, input_url: str) -> Optional[str]:
    media_assets = []
    stype = extract_stream_type(input_url)
    for key in ["media_asset", "media_asset_v2"]:
        asset = player_config.get(key)
        if isinstance(asset, dict):
            media_assets.append(asset)
        elif isinstance(asset, list):
            media_assets.extend(asset)
    for asset in media_assets:
        for key in ["fallback", "primary"]:
            try:
                url = asset[key]["content_url"]
                if not url:
                    continue
                if ".m3u8" not in url and ".mpd" not in url:
                    continue
                base_url = url.split("?")[0]
                if ".mpd" in base_url:
                    return url
                candidates = [
                    base_url.replace("_fhd", "_fhd").replace("/fhd/", "/fhd/"),
                    base_url.replace("_fhd", "_hd").replace("/fhd/", "/hd/").replace("_hd", "_hd"),
                    base_url.replace("_fhd", "_sd").replace("/fhd/", "/sd/").replace("/hd/", "/sd/").replace("_hd", "_sd"),
                ]
                seen = set()
                candidates = [c for c in candidates if not (c in seen or seen.add(c))]
                final_url = candidates[0]
                if stype in ["LIVE TV", "MOVIE", "TV SHOW"]:
                    return url
                elif stype == "REPLAY":
                    clean = url.split("?")[0]
                    path  = clean.rsplit("/", 1)[0]
                    return path + "/index_7.m3u8"
                elif stype in ["HIGHLIGHTS", "CLIP"]:
                    return final_url.split("?")[0]
                return final_url
            except:
                pass
    return None

# ===================== API URL BUILDERS =====================

def build_api_url(slug_path: str, lang: str, quality_choice: str) -> str:
    if quality_choice == "1":
        capabilities = {
            "ads": ["non_ssai"],
            "audio_channel": ["stereo", "dolby51", "atmos"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short", "long"],
            "dynamic_range": ["sdr", "hdr"],
            "encryption": ["widevine", "plain"],
            "ladder": ["tv", "full"],
            "package": ["dash", "hls"],
            "resolution": ["sd", "hd", "fhd", "4k"],
            "true_resolution": ["hd", "4k"],
            "video_codec": ["h265", "h264"],
            "video_codec_non_secure": ["h265", "h264", "vp9"]
        }
    else:
        capabilities = {
            "ads": ["non_ssai", "ssai"],
            "audio_channel": ["stereo"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short"],
            "dynamic_range": ["sdr"],
            "encryption": ["widevine", "plain"],
            "ladder": ["web", "tv", "phone"],
            "package": ["dash", "hls"],
            "resolution": ["sd", "hd", "fhd"],
            "video_codec": ["h264", "h265"],
            "video_codec_non_secure": ["h264", "h265"]
        }
    drm = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
    }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang)
    )

# ===================== FETCH LANG STREAM =====================

def fetch_lang_stream(lang_code: str, lang_name: str, slug_path: str, input_url: str, quality_choice: str, fast: bool = False):
    max_retries = 5 if fast else 8
    for attempt in range(max_retries):
        try:
            api_url = build_api_url(slug_path, lang_code, quality_choice)
            if not fast:
                time.sleep(random.uniform(0.5, 1.2))
            req = request.Request(api_url, headers=build_headers())
            if not fast:
                time.sleep(random.uniform(0.3, 0.8))
            with request.urlopen(req, timeout=12) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            player_config = None
            page_spaces = data.get("success", {}).get("page", {}).get("spaces", {})
            for s in page_spaces:
                for w in page_spaces[s].get("widget_wrappers", []):
                    if "player_config" in w.get("widget", {}).get("data", {}):
                        player_config = w["widget"]["data"]["player_config"]
                        break
                if player_config:
                    break
            if not player_config:
                continue
            clean_stream = extract_best_stream(player_config, input_url)
            if not clean_stream:
                continue
            # Rewrite SSAI / CF / liveNNmp → clean liveNNp.hotstar.com
            _host_l = urlparse(clean_stream).netloc.lower()
            if (
                "live-cf.cdn.hotstar.com" in clean_stream
                or "ssai" in _host_l
                or re.match(r"live\d+m?p-", _host_l)
            ):
                rewritten = rewrite_cdn_to_livehost(clean_stream)
                if rewritten != clean_stream:
                    clean_stream = rewritten
                elif "live-cf.cdn.hotstar.com" in clean_stream:
                    # CF with no usable playback_host — retry API
                    if attempt < max_retries - 5:
                        time.sleep(random.uniform(0.5, 1.5))
                    continue
            audio_lang = ""
            try:
                _url_segs = set(clean_stream.lower().split("?")[0].replace("https://","").split("/"))
                for code, name in LANGUAGES.items():
                    if code.lower() in _url_segs:
                        audio_lang = name
                        break
                if not audio_lang:
                    _ptags = str(player_config.get("playback_tags", "")).lower()
                    for _tag in _ptags.split(";"):
                        if _tag.strip().startswith("language:"):
                            _detected = _tag.split(":")[1].strip()
                            audio_lang = LANGUAGES.get(_detected, "")
                            break
            except:
                pass
            is_hdr = False
            dynamic_range = player_config.get("dynamic_range", "").lower()
            if dynamic_range == "hdr":
                is_hdr = True
            elif "hdr" in str(player_config.get("playback_tags", "")).lower():
                is_hdr = True
            elif "hdr" in clean_stream.lower():
                is_hdr = True
            return {"lang_name": audio_lang or lang_name, "stream": clean_stream, "player_config": player_config, "is_hdr": is_hdr}
        except:
            pass
    return None

# ===================== HDNTL TOKEN HELPERS =====================

def _find_license_url(obj, depth=0) -> str:
    if depth > 8 or not isinstance(obj, (dict, list)):
        return ""
    if isinstance(obj, list):
        for value in obj:
            found = _find_license_url(value, depth + 1)
            if found:
                return found
        return ""
    for key in (
        "license_url", "licenseUrl", "widevine_license_url",
        "keyServerUrl", "key_server_url", "keyserver_url",
        "drm_license_url", "drmLicenseUrl",
    ):
        if obj.get(key):
            return str(obj[key])
    for value in obj.values():
        found = _find_license_url(value, depth + 1)
        if found:
            return found
    return ""


def _kids_from_pssh_b64(pssh_b64: str) -> list:
    """Extract KIDs from Widevine PSSH base64 (v0 protobuf + v1 KID list)."""
    import base64 as _b64p
    kids = []
    try:
        data = _b64p.b64decode(pssh_b64 + "==")
        WV_SID = bytes.fromhex("edef8ba979d64acea3c827dcd51d21ed")
        pos = data.find(WV_SID)
        if pos == -1:
            return kids
        vf_pos = pos - 4
        if vf_pos < 0:
            return kids
        version = data[vf_pos]
        after_sid = pos + 16
        if version == 1:
            if after_sid + 4 > len(data):
                return kids
            kid_count = int.from_bytes(data[after_sid:after_sid + 4], "big")
            offset = after_sid + 4
            for _ in range(min(kid_count, 64)):
                if offset + 16 > len(data):
                    break
                kids.append(data[offset:offset + 16].hex())
                offset += 16
        else:
            if after_sid + 4 > len(data):
                return kids
            i = after_sid + 4
            while i < len(data) - 17:
                if data[i] == 0x12 and data[i + 1] == 0x10:
                    kids.append(data[i + 2:i + 18].hex())
                    i += 18
                else:
                    i += 1
    except Exception:
        pass
    return kids


def _fetch_mpd_pssh_info(mpd_url: str) -> dict:
    """
    Download MPD and extract PSSH + all KIDs (XML attrs, Widevine PSSH, PlayReady).
    Mirrors hot.py fetch_mpd_pssh for reliable ClearKey lookups.
    """
    try:
        token = extract_hdntl_from_url(mpd_url)
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Referer": M3U_REFERER,
            "Origin": M3U_ORIGIN,
            "Accept": "*/*",
        }
        if token:
            headers["Cookie"] = f"hdntl={token}"
        req = request.Request(mpd_url, headers=headers)
        with request.urlopen(req, timeout=15) as resp:
            mpd_text = resp.read().decode("utf-8", errors="replace")

        pssh = ""
        wv_block = re.search(
            r'(?:edef8ba9|EDEF8BA9).{0,200}?<cenc:pssh[^>]*>(.*?)</cenc:pssh>',
            mpd_text, re.DOTALL,
        )
        if not wv_block:
            wv_block = re.search(r'<cenc:pssh[^>]*>(.*?)</cenc:pssh>', mpd_text, re.DOTALL)
        if wv_block:
            pssh = wv_block.group(1).strip()

        key_ids = []
        kid_patterns = [
            r'default_KID="([0-9a-fA-F\-]{32,36})"',
            r'cenc:default_KID="([0-9a-fA-F\-]{32,36})"',
            r'default_KID="\{([0-9a-fA-F\-]{32,36})\}"',
            r'cenc:default_KID="\{([0-9a-fA-F\-]{32,36})\}"',
            r'<ContentProtection[^>]+value="([0-9a-fA-F]{32})"',
            r'<ContentProtection[^>]+value="\{([0-9a-fA-F\-]{32,36})\}"',
        ]
        for pat in kid_patterns:
            for m in re.finditer(pat, mpd_text):
                kid = m.group(1).replace("-", "").lower()
                if len(kid) == 32 and kid not in key_ids:
                    key_ids.append(kid)

        if pssh:
            for kid in _kids_from_pssh_b64(pssh):
                kid = kid.lower()
                if len(kid) == 32 and kid not in key_ids:
                    key_ids.append(kid)
        for pssh_b64_raw in re.findall(r'<cenc:pssh[^>]*>(.*?)</cenc:pssh>', mpd_text, re.DOTALL):
            for kid in _kids_from_pssh_b64(pssh_b64_raw.strip()):
                kid = kid.lower()
                if len(kid) == 32 and kid not in key_ids:
                    key_ids.append(kid)

        # PlayReady mspr:pro — little-endian GUID → big-endian hex KID
        import base64 as _b64pr
        for pro_b64 in re.findall(
            r'<(?:mspr:pro|[^>]*:pro)[^>]*>(.*?)</(?:mspr:pro|[^>]*:pro)>',
            mpd_text, re.DOTALL,
        ):
            try:
                pro_bytes = _b64pr.b64decode(pro_b64.strip() + "==")
                pr_xml = pro_bytes.decode("utf-16-le", errors="replace")
                for m in re.finditer(r'<KID[^>]+VALUE="([A-Za-z0-9+/=]{24,})"', pr_xml):
                    try:
                        raw = _b64pr.b64decode(m.group(1) + "==")
                        if len(raw) == 16:
                            kid_hex = (
                                raw[3::-1].hex()
                                + raw[5:3:-1].hex()
                                + raw[7:5:-1].hex()
                                + raw[8:].hex()
                            )
                            if len(kid_hex) == 32 and kid_hex not in key_ids:
                                key_ids.append(kid_hex)
                    except Exception:
                        pass
            except Exception:
                pass

        has_clearkey = "1077efec" in mpd_text.lower() or "clearkey" in mpd_text.lower()
        return {
            "pssh": pssh,
            "key_ids": key_ids,
            "has_clearkey": has_clearkey,
            "error": None,
        }
    except Exception as e:
        return {"pssh": "", "key_ids": [], "has_clearkey": False, "error": str(e)}


def _direct_urlopen(req, timeout=15):
    """HTTP call that bypasses the global proxy (license servers often fail via proxy)."""
    try:
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        return opener.open(req, timeout=timeout)
    except Exception:
        # Fallback to default opener if direct fails
        return request.urlopen(req, timeout=timeout)


def _parse_clearkey_response(payload, kid_list: list) -> list:
    import base64 as _b64
    result = []
    # Standard ClearKey JSON: {"keys":[{"k":"...","kid":"..."}]}
    for item in payload.get("keys", []) if isinstance(payload, dict) else []:
        key_b64 = item.get("k", "")
        kid_b64 = item.get("kid", "")
        if not key_b64:
            continue
        try:
            key_hex = _b64.urlsafe_b64decode(key_b64 + "==").hex()
            kid_hex = (
                _b64.urlsafe_b64decode(kid_b64 + "==").hex()
                if kid_b64 else kid_list[0].replace("-", "").lower()
            )
            result.append(f"{kid_hex}:{key_hex}")
        except Exception:
            continue
    # Some servers return flat {kid: key} hex maps
    if not result and isinstance(payload, dict):
        for k, v in payload.items():
            if k in ("keys", "type", "status"):
                continue
            if isinstance(k, str) and isinstance(v, str) and len(k.replace("-", "")) == 32:
                result.append(f"{k.replace('-', '').lower()}:{v.replace('-', '').lower()}")
    return result


# Cache: avoid hammering license server (429) for same content / multiple langs
_DRM_KEY_CACHE: dict = {}
_DRM_CACHE_LOCK = threading.Lock()


def _drm_cache_key(license_url: str, kid_list: list, pssh: str = "") -> str:
    kids = ",".join(sorted(k.replace("-", "").lower() for k in (kid_list or [])))
    try:
        path = urlparse(license_url).path
    except Exception:
        path = license_url or ""
    return f"{path}|{kids}|{(pssh or '')[:48]}"


def _fetch_clearkey(kid_list: list, license_url: str, last_error: list = None) -> list:
    """
    Single ClearKey JSON attempt (proxy-bypassed).
    Multi-variant spam caused HTTP 429 on apix.hotstar.com — keep it lean.
    """
    if not kid_list or not license_url:
        if last_error is not None:
            last_error.append("missing license_url or kids")
        return []
    import base64 as _b64
    b64_kids = [
        _b64.urlsafe_b64encode(bytes.fromhex(kid.replace("-", ""))).rstrip(b"=").decode()
        for kid in kid_list
    ]
    body = json.dumps({"kids": b64_kids, "type": "temporary"}).encode()
    headers = {
        "Content-Type": "application/json",
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        "Referer": "https://www.hotstar.com/",
        "Origin": "https://www.hotstar.com",
        "Accept": "*/*",
    }
    try:
        req = request.Request(license_url, data=body, headers=headers, method="POST")
        with _direct_urlopen(req, timeout=15) as resp:
            raw = resp.read()
        try:
            payload = json.loads(raw.decode("utf-8", errors="replace"))
        except Exception:
            if last_error is not None:
                last_error.append(f"non-json response ({len(raw)} bytes)")
            return []
        keys = _parse_clearkey_response(payload, kid_list)
        if not keys and last_error is not None:
            last_error.append(f"empty keys: {str(payload)[:100]}")
        return keys
    except Exception as e:
        code = getattr(e, "code", None)
        msg = f"HTTP {code}: {e}" if code else str(e)
        if last_error is not None:
            last_error.append(msg)
        return []


def _find_device_wvd() -> Optional[str]:
    """Locate device.wvd (or aliases) next to script / cwd / home."""
    names = ["device.wvd", "wv.wvd", "chrome.wvd", "cdm.wvd"]
    bases = [
        _SCRIPT_DIR,
        os.getcwd(),
        os.path.expanduser("~"),
        os.path.join(os.path.expanduser("~"), "tokens"),
    ]
    for base in bases:
        for name in names:
            p = os.path.join(base, name)
            if os.path.isfile(p):
                return p
    return None


def _key_to_hex(val) -> str:
    """Normalize pywidevine kid/key (bytes, UUID, hex str) → hex string."""
    if val is None:
        return ""
    try:
        if isinstance(val, (bytes, bytearray)):
            return bytes(val).hex()
        if hasattr(val, "bytes") and not isinstance(val, (str, int)):
            return val.bytes.hex()  # uuid.UUID
        hex_fn = getattr(val, "hex", None)
        if callable(hex_fn):
            h = hex_fn()
            return h if isinstance(h, str) else bytes(h).hex()
        if isinstance(val, str):
            return val.replace("-", "").lower()
        return bytes(val).hex()
    except Exception:
        try:
            return str(val).replace("-", "").lower()
        except Exception:
            return ""


def _fetch_widevine_keys(pssh_b64: str, license_url: str, last_error: list = None) -> list:
    """
    Widevine CDM via pywidevine + device.wvd (hot.py style).
    License POST always goes direct (no proxy).
    """
    try:
        from pywidevine.cdm import Cdm
        from pywidevine.device import Device
        from pywidevine.pssh import PSSH as WvPSSH
    except ImportError:
        if last_error is not None:
            last_error.append("pywidevine not installed → pip install pywidevine")
        return []
    if not pssh_b64:
        if last_error is not None:
            last_error.append("No PSSH for Widevine challenge")
        return []
    device_path = _find_device_wvd()
    if not device_path:
        if last_error is not None:
            last_error.append("No device.wvd found (place next to script or in ~)")
        return []
    try:
        device = Device.load(device_path)
        cdm = Cdm.from_device(device)
        session_id = cdm.open()
        pssh_obj = WvPSSH(pssh_b64)
        challenge = cdm.get_license_challenge(session_id, pssh_obj)
        headers = {
            "Content-Type": "application/octet-stream",
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Referer": "https://www.hotstar.com/",
            "Origin": "https://www.hotstar.com",
            "Accept": "*/*",
        }
        lic_req = request.Request(license_url, data=challenge, headers=headers, method="POST")
        with _direct_urlopen(lic_req, timeout=20) as resp:
            license_bytes = resp.read()
        if not license_bytes:
            cdm.close(session_id)
            if last_error is not None:
                last_error.append("Widevine empty license body")
            return []
        cdm.parse_license(session_id, license_bytes)

        keys = []
        seen = set()
        raw_types = []
        for k in cdm.get_keys(session_id):
            t_raw = getattr(k, "type", None)
            # Enum → .name == "CONTENT"; str(enum) was "KeyType.CONTENT" and failed exact match
            t_name = str(getattr(t_raw, "name", t_raw) or "").upper()
            raw_types.append(t_name or "?")
            if t_name and "SIGN" in t_name:
                continue
            kid = _key_to_hex(getattr(k, "kid", None))
            key = _key_to_hex(getattr(k, "key", None))
            if not kid or not key:
                continue
            pair = f"{kid}:{key}"
            if pair not in seen:
                seen.add(pair)
                keys.append(pair)
        cdm.close(session_id)

        if not keys and last_error is not None:
            last_error.append(
                f"Widevine license OK but no usable keys (types={raw_types}, bytes={len(license_bytes)})"
            )
        return keys
    except Exception as e:
        if last_error is not None:
            last_error.append(f"Widevine: {e}")
        return []



def build_drm_api_url(slug_path: str, lang: str = "eng") -> str:
    """Widevine-capable client_capabilities — returns MPD + license_url."""
    capabilities = {
        "ads": ["non_ssai"],
        "audio_channel": ["stereo", "dolby51", "atmos"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short", "long"],
        "dynamic_range": ["sdr", "hdr"],
        "encryption": ["widevine", "plain"],
        "ladder": ["tv", "full"],
        "package": ["dash", "hls"],
        "resolution": ["sd", "hd", "fhd", "4k"],
        "true_resolution": ["hd", "4k"],
        "video_codec": ["h265", "h264"],
        "video_codec_non_secure": ["h265", "h264", "vp9"],
    }
    drm = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"],
    }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang)
    )


def _fetch_license_from_drm_api(slug_path: str, lang: str = "eng") -> str:
    """Hit DRM-capable watch API and pull license_url from player_config."""
    if not slug_path:
        return ""
    try:
        api_url = build_drm_api_url(slug_path, lang)
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=12) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                d = w.get("widget", {}).get("data", {})
                if "player_config" in d:
                    lic = _find_license_url(d["player_config"])
                    if lic:
                        return lic
                    # media_asset primary/fallback
                    for key in ("media_asset", "media_asset_v2"):
                        assets = d["player_config"].get(key)
                        if isinstance(assets, dict):
                            assets = [assets]
                        if not isinstance(assets, list):
                            continue
                        for asset in assets:
                            if not isinstance(asset, dict):
                                continue
                            for variant in ("primary", "fallback"):
                                item = asset.get(variant) or {}
                                if isinstance(item, dict):
                                    for k in ("license_url", "licenseUrl", "keyServerUrl"):
                                        if item.get(k):
                                            return str(item[k])
    except Exception:
        pass
    return ""


def _embed_drm_in_url(stream_url: str, key_str: str, hdntl: str = "") -> str:
    """Build playable MPD URL with ClearKey + single clean hdntl cookie (no double Cookie=)."""
    tok = _strip_hdntl_prefix(hdntl or extract_hdntl_from_url(stream_url) or "")
    raw = (stream_url or "").split("|")[0].strip()
    # keep path; rebuild query cleanly
    base_path = raw.split("?")[0]
    q = []
    if tok:
        q.append(f"hdnea={tok}")
    # optional short markers
    q.append("a=ns")
    url = base_path + ("?" + "&".join(q) if q else "")
    # pipe extras for NS / TiviMate-style players
    pipe = []
    if tok:
        pipe.append(f"Cookie=hdntl={tok}")
    pipe.append(f"User-Agent={M3U_USER_AGENT}")
    pipe.append(f"Referer={M3U_REFERER}")
    pipe.append(f"Origin={M3U_ORIGIN}")
    if key_str:
        pipe.append("drmScheme=clearkey")
        pipe.append(f"drmLicense={key_str}")
    if pipe:
        url = url + "|" + "&".join(pipe)
    return url


def _fetch_drm_details(mpd_url: str, player_config: dict, slug_path: str = "") -> dict:
    """
    For MPD streams: KIDs + keys via ClearKey, then Widevine (device.wvd).
    Caches results so multi-language fetches don't 429 the license server.
    """
    check = (mpd_url or "").split("|")[0].lower()
    if ".mpd" not in check:
        return {}

    license_url = _find_license_url(player_config)
    if not license_url:
        for key in ("media_asset", "media_asset_v2"):
            assets = player_config.get(key)
            if not assets:
                continue
            if isinstance(assets, dict):
                assets = [assets]
            for asset in assets:
                if not isinstance(asset, dict):
                    continue
                for variant in ("primary", "fallback"):
                    item = asset.get(variant)
                    if isinstance(item, dict):
                        lic = (
                            item.get("license_url")
                            or item.get("licenseUrl")
                            or item.get("keyServerUrl")
                            or ""
                        )
                        if lic:
                            license_url = lic
                            break
                if license_url:
                    break
            if license_url:
                break

    if not license_url and slug_path:
        license_url = _fetch_license_from_drm_api(slug_path)

    mpd_info = _fetch_mpd_pssh_info(mpd_url.split("|")[0])
    key_ids = mpd_info.get("key_ids") or []
    pssh = mpd_info.get("pssh") or ""
    keys = []
    err_detail = []
    method = ""

    if key_ids and license_url:
        cache_key = _drm_cache_key(license_url, key_ids, pssh)
        with _DRM_CACHE_LOCK:
            cached = _DRM_KEY_CACHE.get(cache_key)
        if cached:
            keys = list(cached)
            method = "cache"
        else:
            # Hotstar apix license: prefer Widevine first (ClearKey often 429)
            is_hotstar_lic = "apix.hotstar.com" in (license_url or "") or "hotstar.com" in (license_url or "")
            if is_hotstar_lic and pssh:
                keys = _fetch_widevine_keys(pssh, license_url, last_error=err_detail)
                if keys:
                    method = "widevine"
            if not keys:
                # brief pause then one ClearKey try
                time.sleep(0.4)
                ck_err = []
                keys = _fetch_clearkey(key_ids, license_url, last_error=ck_err)
                if keys:
                    method = "clearkey"
                else:
                    err_detail.extend(ck_err)
            if not keys and pssh and not (is_hotstar_lic and method == ""):
                # last resort Widevine if not already tried
                if method != "widevine":
                    keys = _fetch_widevine_keys(pssh, license_url, last_error=err_detail)
                    if keys:
                        method = "widevine"
            if keys:
                with _DRM_CACHE_LOCK:
                    _DRM_KEY_CACHE[cache_key] = list(keys)
            else:
                time.sleep(1.0)  # cool-down after failure (avoid 429 chain)
    elif key_ids and not license_url:
        err_detail.append("no license_url in player_config or DRM API")

    is_encrypted = bool(key_ids) or bool(pssh) or mpd_info.get("has_clearkey")
    if not is_encrypted and not keys:
        return {}

    return {
        "is_drm": True,
        "keys": keys,
        "key_ids": key_ids,
        "license_url": license_url,
        "pssh": pssh,
        "method": method,
        "error": err_detail[0] if err_detail else "",
    }

def get_hdntl_token_4kads(url: str, retries=5) -> str:
    """Fetch hdntl from CDN Set-Cookie via PROXY (same egress IP as playback)."""
    if not url:
        return ""
    headers = {
        "User-Agent": HEADERS_BASE_4KADS.get(
            "User-Agent",
            "Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)",
        ),
        "Referer": "https://www.hotstar.com/",
        "Origin": "https://www.hotstar.com",
        "Accept": "*/*",
    }
    target = url.split("|")[0].strip()
    # try original + https upgrade (some CDNs only set cookie on https)
    targets = [target]
    if target.startswith("http://"):
        targets.append("https://" + target[len("http://"):])
    for attempt in range(max(1, retries)):
        for tgt in targets:
            try:
                req = request.Request(tgt, headers=headers)
                with request.urlopen(req, timeout=15) as resp:
                    sc = resp.headers.get("Set-Cookie") or ""
                    try:
                        all_sc = resp.headers.get_all("Set-Cookie") or []
                        if all_sc:
                            sc = "\n".join(all_sc)
                    except Exception:
                        pass
                    m = re.search(r"hdntl=([^;\s]+)", sc, flags=re.I)
                    if m and "exp=" in m.group(1):
                        return m.group(1).strip()
                    loc = resp.headers.get("Location") or ""
                    if loc and ("hdnea=" in loc or "hdntl=" in loc):
                        t2 = extract_hdntl_from_url(loc) or ""
                        if t2 and "exp=" in t2:
                            return t2
            except Exception:
                continue
        if attempt + 1 < retries:
            time.sleep(0.35)
    try:
        t3 = extract_hdntl_from_url(target) or ""
        if t3 and "exp=" in t3:
            return t3
    except Exception:
        pass
    return ""


# ===================== CDN REWRITE (live-cf → live*.hotstar.com) =====================

_CDN_HOSTS_SET = {
    "live07p.hotstar.com", "live08p.hotstar.com", "live09p.hotstar.com",
    "live10p.hotstar.com", "live11p.hotstar.com", "live12p.hotstar.com",
    "live13p.hotstar.com", "live14p.hotstar.com", "live15p.hotstar.com",
    "live16p.hotstar.com", "live17p.hotstar.com", "live18p.hotstar.com",
    "live19p.hotstar.com", "live20p.hotstar.com", "live21p.hotstar.com",
    "live22p.hotstar.com", "live23p.hotstar.com", "live24p.hotstar.com",
    # non-p + jio edge (episode live / 15min DVR)
    "live07.hotstar.com", "live08.hotstar.com", "live09.hotstar.com",
    "live10.hotstar.com", "live11.hotstar.com", "live12.hotstar.com",
    "live13.hotstar.com", "live14.hotstar.com", "live15.hotstar.com",
    "live16.hotstar.com", "live17.hotstar.com", "live18.hotstar.com",
    "live19.hotstar.com", "live20.hotstar.com",
    "live-jiol.cdn.hotstar.com", "live-jio.cdn.hotstar.com",
}
_CF_STRIP_PARAMS = {"signature", "expires", "key-pair-id"}

def _extract_live_prefix(playback_host: str) -> str:
    """Extract clean live prefix: live12p / live12mp → live12p; live-jiol → jiol."""
    h = playback_host or ""
    # live12p / live12mp / live12 → live12p (mp stripped)
    m = re.match(r"(live\d+)m?p?(?:-|\.|$)", h, re.I)
    if m:
        return m.group(1).lower() + "p"
    if "live-jiol" in h.lower():
        return "live-jiol.cdn"
    return ""

def rewrite_cdn_to_livehost(url: str) -> str:
    """Rewrite SSAI/CF URL → clean liveXXp.hotstar.com.

    Prefix from:
      1. playback_host=live12mp-... / live12p-... → live12p
      2. netloc live12mp-ssai-... / live12p-ssai-... → live12p
    """
    try:
        parsed = urlparse(url)
        raw_query = parsed.query or ""
        live_prefix = ""

        ph_match = re.search(r'(?:^|&)playback_host=([^&]+)', raw_query)
        if ph_match:
            live_prefix = _extract_live_prefix(unquote(ph_match.group(1)))

        if not live_prefix:
            live_prefix = _extract_live_prefix(parsed.netloc or "")

        if not live_prefix:
            return url
        if live_prefix == "live-jiol.cdn":
            clean_host = "live-jiol.cdn.hotstar.com"
        else:
            clean_host = f"{live_prefix}.hotstar.com"
        # allow rewrite even if host not pre-listed (live07–99)
        if clean_host not in _CDN_HOSTS_SET and not re.match(r"live\d+p\.hotstar\.com$", clean_host):
            if clean_host != "live-jiol.cdn.hotstar.com":
                return url
        kept_parts = []
        for part in raw_query.split("&"):
            if not part:
                continue
            key = part.split("=", 1)[0].strip().lower()
            if key in _CF_STRIP_PARAMS:
                continue
            kept_parts.append(part)
        new_query = "&".join(kept_parts)
        return urlunparse(parsed._replace(netloc=clean_host, query=new_query))
    except Exception:
        return url

def append_hdntl_to_url_4kads(base_url: str, token: str) -> str:
    if not token:
        return base_url
    if '?' in base_url:
        base_part, query_part = base_url.split('?', 1)
        params = query_part.split('&')
        new_params = [p for p in params if not (p.startswith('hdnea=') or p.startswith('hdntl=') or p.startswith('ttl=') or p.startswith('Expires=') or p.startswith('Signature=') or p.startswith('Key-Pair-Id='))]
        base_url = base_part + ('?' + '&'.join(new_params) if new_params else '')
    if '?' in base_url:
        return base_url + '&hdnea=' + token
    else:
        return base_url + '?hdnea=' + token

def _embed_hdntl_in_url(url: str) -> str:
    """option7: Set-Cookie hdntl → embed as hdnea on URL. Always prefer a token on the URL."""
    raw = (url or "").split("|")[0].strip()
    if not raw:
        return url
    existing = ""
    try:
        existing = extract_hdntl_from_url(raw) or ""
        existing = _strip_hdntl_prefix(existing) if existing else ""
    except Exception:
        existing = ""
    token = get_hdntl_token_4kads(raw, retries=5)
    if token:
        try:
            token = _strip_hdntl_prefix(token)
        except Exception:
            pass
    use = token or existing
    if use:
        return append_hdntl_to_url_4kads(raw, use)
    return raw


def _ensure_4k_token(url: str) -> str:
    """
    option7 style: KEEP API-issued path-ACL hdnea (acl=/out/v1/... or acl=/cmaf/...).
    Never replace with Set-Cookie acl=/* — that breaks SSAI 4K playback.
    Only probe Set-Cookie when URL has no token at all.
    """
    raw = (url or "").split("|")[0].strip()
    if not raw:
        return ""
    tok = ""
    try:
        tok = extract_hdntl_from_url(raw) or ""
        tok = _strip_hdntl_prefix(tok) if tok else ""
    except Exception:
        tok = ""
    if tok and "exp=" in tok:
        # path-specific ACL or any valid API token → keep as-is (option7 working style)
        return raw
    # no token — try Set-Cookie once
    out = _embed_hdntl_in_url(raw)
    if out and ("hdnea=" in out.lower() or "hdntl=" in out.lower()):
        return out
    return ""


def _lang_from_stream_url(url: str, fallback: str = "") -> str:
    """Detect language from Hotstar CDN path (/eng/, biggboss-kan-2026/, etc.)."""
    u = (url or "").lower()
    pairs = [
        ("/eng/", "ENGLISH"), ("/en/", "ENGLISH"),
        ("/hin/", "HINDI"), ("/hi/", "HINDI"),
        ("/mar/", "MARATHI"), ("/mr/", "MARATHI"),
        ("/tam/", "TAMIL"), ("/ta/", "TAMIL"),
        ("/tel/", "TELUGU"), ("/te/", "TELUGU"),
        ("/kan/", "KANNADA"), ("/kn/", "KANNADA"),
        ("/mal/", "MALAYALAM"), ("/ml/", "MALAYALAM"),
        ("/ben/", "BENGALI"), ("/bn/", "BENGALI"),
        ("/pan/", "PUNJABI"), ("/pun/", "PUNJABI"),
        ("/guj/", "GUJARATI"), ("/bho/", "BHOJPURI"),
        ("/har/", "HARYANVI"), ("/hv/", "HARYANVI"),
        ("language=english", "ENGLISH"), ("language=hindi", "HINDI"),
        ("language=tamil", "TAMIL"), ("language=telugu", "TELUGU"),
        ("language=kannada", "KANNADA"), ("language=malayalam", "MALAYALAM"),
        ("language=bengali", "BENGALI"), ("language=marathi", "MARATHI"),
        ("language=gujarati", "GUJARATI"), ("language=bhojpuri", "BHOJPURI"),
        ("language=punjabi", "PUNJABI"), ("language=haryanvi", "HARYANVI"),
        ("english4k", "ENGLISH"), ("hindi4k", "HINDI"),
        ("-eng-", "ENGLISH"), ("-hin-", "HINDI"),
        ("-tam-", "TAMIL"), ("-tel-", "TELUGU"),
        ("-kan-", "KANNADA"), ("-mal-", "MALAYALAM"),
        ("-ben-", "BENGALI"), ("-mar-", "MARATHI"),
        ("-pun-", "PUNJABI"), ("-pan-", "PUNJABI"),
        ("-har-", "HARYANVI"), ("-bho-", "BHOJPURI"), ("-guj-", "GUJARATI"),
    ]
    for needle, name in pairs:
        if needle in u:
            return name
    fb = (fallback or "").strip()
    return fb.upper() if fb else ""


def _hq_logo(img) -> str:
    """Normalize path/URL → full-quality logo without Cloudinary transforms."""
    if not img:
        return ""
    if isinstance(img, dict):
        s = str(
            img.get("h")
            or img.get("horizontal")
            or img.get("src")
            or img.get("url")
            or img.get("i")
            or img.get("b")
            or ""
        ).strip()
    else:
        s = str(img).strip()
    if not s:
        return ""
    path = s
    if "image/upload/" in path:
        path = path.split("image/upload/", 1)[1]
        # strip f_auto / t_web_* / q_* / w_* transform prefixes
        while path and re.match(r"^[ftqwhc]_", path):
            parts = path.split("/", 1)
            path = parts[1] if len(parts) > 1 else ""
    path = path.lstrip("/")
    if not path:
        return ""
    return f"https://img1.hotstarext.com/image/upload/{path}"


def _logo_asset_suffix(p: str) -> str:
    """Last path segment suffix: h / b / t / v / i / ''."""
    if not p:
        return ""
    s = str(p).split("?")[0].rstrip("/")
    last = s.rsplit("/", 1)[-1]
    last = re.sub(r"\.(?:jpg|jpeg|png|webp)$", "", last, flags=re.I)
    m = re.search(r"-([a-z])$", last, flags=re.I)
    return (m.group(1).lower() if m else "")


def _is_h_logo_path(p: str) -> bool:
    """True for horizontal assets (.../123456-h)."""
    return _logo_asset_suffix(p) == "h"


def _is_bad_logo_path(p: str) -> bool:
    """Reject small/thumb assets (-t -b -v -i)."""
    return _logo_asset_suffix(p) in ("t", "b", "v", "i")


def _collect_image_candidates(obj, depth=0, found=None) -> list:
    """Deep-walk API JSON for image paths. Prefer -h."""
    if found is None:
        found = []
    if depth > 14 or obj is None:
        return found
    if isinstance(obj, dict):
        # images: {h, b, t, ...} — PHP uses images.h
        images = obj.get("images")
        if isinstance(images, dict):
            for key in ("h", "horizontal", "landscape", "b", "t", "v", "i"):
                val = images.get(key)
                if isinstance(val, str) and val.strip():
                    suf = _logo_asset_suffix(val) or (key if key in "hbtvi" else "m")
                    rank = "h" if (key == "h" or suf == "h") else ("b" if suf in "btvi" else "m")
                    found.append((rank, val.strip()))
                elif isinstance(val, dict):
                    src = val.get("src") or val.get("url") or ""
                    if src:
                        found.append(("h" if _is_h_logo_path(src) else "b", str(src).strip()))
        for prefer_key in ("h", "horizontal", "landscape", "poster_h", "image_h"):
            val = obj.get(prefer_key)
            if isinstance(val, str) and val.strip():
                found.append(("h", val.strip()))
            elif isinstance(val, dict):
                src = val.get("src") or val.get("url") or ""
                if src:
                    found.append(("h" if _is_h_logo_path(src) else "m", str(src).strip()))
        for k, val in obj.items():
            kl = str(k).lower()
            if kl in ("src", "url", "href") and isinstance(val, str):
                if "cms/prod" in val or "image/upload" in val or "-h" in val or "-t" in val or "-b" in val:
                    suf = _logo_asset_suffix(val)
                    rank = "h" if suf == "h" else ("b" if suf in "btvi" else "m")
                    found.append((rank, val.strip()))
            elif isinstance(val, dict) and any(x in kl for x in ("image", "poster", "thumb", "logo", "artwork")):
                src = val.get("src") or val.get("url") or ""
                if src:
                    suf = _logo_asset_suffix(src)
                    rank = "h" if suf == "h" else ("b" if suf in "btvi" else "m")
                    found.append((rank, str(src).strip()))
            elif kl not in ("images",):
                _collect_image_candidates(val, depth + 1, found)
    elif isinstance(obj, list):
        for item in obj[:100]:
            _collect_image_candidates(item, depth + 1, found)
    elif isinstance(obj, str):
        if "cms/prod" in obj or "/image/upload/" in obj:
            suf = _logo_asset_suffix(obj)
            rank = "h" if suf == "h" else ("b" if suf in "btvi" else "m")
            found.append((rank, obj))
    return found


def _pick_best_logo(candidates: list) -> str:
    """Prefer -h, then -b (cast_image), never prefer -t (title_cutout)."""
    if not candidates:
        return ""
    seen = set()
    h_list, b_list, other, t_list = [], [], [], []
    for rank, path in candidates:
        key = path.split("?")[0]
        if key in seen or len(path) < 8:
            continue
        seen.add(key)
        suf = _logo_asset_suffix(path)
        if suf == "h" or (rank == "h" and suf not in ("t", "b", "v", "i")):
            if suf == "h":
                h_list.append(path)
            elif suf == "b":
                b_list.append(path)
            elif suf == "t":
                t_list.append(path)
            else:
                other.append(path)
        elif suf == "b":
            b_list.append(path)
        elif suf == "t":
            t_list.append(path)
        else:
            other.append(path)
    for group in (h_list, b_list, other, t_list):
        if group:
            group.sort(key=lambda p: (0 if "cms/prod" in p else 1, -len(p)))
            return _hq_logo(group[0])
    return ""


def extract_logo_from_player_config(player_config: dict) -> str:
    if not isinstance(player_config, dict):
        return ""
    return _pick_best_logo(_collect_image_candidates(player_config))


def extract_logo_from_api_data(data: dict) -> str:
    if not isinstance(data, dict):
        return ""
    return _pick_best_logo(_collect_image_candidates(data))


def extract_logo_from_url(url: str) -> str:
    """Fetch watch API + deep scan for logo. Prefer -h src."""
    slug_path = extract_slug_path(url)
    if not slug_path:
        return ""
    try:
        api_url = build_api_url(slug_path, "eng", "2")
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=12) as resp:
            data = json.loads(resp.read().decode("utf-8"))

        logo = extract_logo_from_api_data(data)
        if logo and _is_h_logo_path(logo):
            return logo

        page_spaces = data.get("success", {}).get("page", {}).get("spaces", {})
        for s in page_spaces:
            for w in page_spaces[s].get("widget_wrappers", []):
                pc = (w.get("widget") or {}).get("data", {}).get("player_config")
                if pc:
                    logo2 = extract_logo_from_player_config(pc)
                    if logo2 and _is_h_logo_path(logo2):
                        return logo2
                    if logo2 and not logo:
                        logo = logo2

        raw = json.dumps(data)
        # Prefer explicit -h src/url
        for pat in (
            r'"(?:src|url|h)"\s*:\s*"(?:https?://[^"]+/image/upload/)?(sources/r\d+/cms/prod/\d+/\d+-h)"',
            r'"(?:src|url|h)"\s*:\s*"(?:https?://[^"]+/image/upload/)?([^"]*?/\d+-h)"',
            r'(sources/r\d+/cms/prod/\d+/\d+-h)',
            r'(cms/prod/\d+/\d+-h)',
        ):
            for h in re.findall(pat, raw):
                if _is_h_logo_path(h):
                    return _hq_logo(h)

        if logo:
            return logo
    except Exception:
        pass
    return ""


# ===================== M3U FILE CREATION =====================
M3U_USER_AGENT = "Hotstar;in.startv.hotstar/25.02.24.8.11169@rtxcric(Android/15)"
M3U_REFERER = "https://www.hotstar.com/"
M3U_ORIGIN = "https://www.hotstar.com"

def create_m3u_file(entries: List[Tuple[str, str, bool]], title: str, match_no: str,
                    stream_type: str, filename: str = "hotstar_live.m3u", logo_url: str = "",
                    hdntl_cookie: str = "", skip_http_headers: bool = False,
                    force_no_cookie: bool = False, is_adsfree_4k: bool = False) -> bool:
    if not entries:
        print(f"{RED}No stream entries to save.{RESET}")
        return False
    try:
        with open(filename, "w", encoding="utf-8") as f:
            f.write("#EXTM3U\n")
            f.write(f"# Playlist generated by Hotstar Extractor\n")
            f.write(f"# Playlist Created By @rtxcric\n")
            f.write(f"# Title: {title}\n")
            if match_no:
                f.write(f"# Match: {match_no}\n")
            f.write(f"# Type: {stream_type}\n")
            f.write(f"# Generated: {datetime.now(IST).strftime('%Y-%m-%d %I:%M:%S %p')}\n\n")
            import hashlib
            for entry in entries:
                try:
                    if len(entry) == 3:
                        lang, url, is_hdr = entry
                    else:
                        lang, url = entry[0], entry[1]
                        is_hdr = False
                except Exception:
                    continue
                if lang == "__TITLE__":
                    continue
                tvg_id = str(int(hashlib.md5(url.encode()).hexdigest(), 16) % 9999999999)
                lang_upper = lang.upper()
                if is_adsfree_4k:
                    if "SDR" in lang_upper:
                        base_lang = lang.replace(" SDR", "").replace(" sdr", "").strip()
                        channel_label = f"{base_lang} 4K SDR ADSFREE"
                    elif is_hdr:
                        base_lang = lang.replace(" HDR", "").replace(" hdr", "").strip()
                        channel_label = f"{base_lang} 4K HDR ADSFREE"
                    else:
                        channel_label = f"{lang} 4K SDR ADSFREE"
                elif "SDR" in lang_upper:
                    base_lang = lang.replace(" SDR", "").replace(" sdr", "").strip()
                    channel_label = f"{base_lang} SDR"
                elif is_hdr:
                    channel_label = f"{lang} HDR"
                else:
                    channel_label = f"{lang}"

                if hdntl_cookie:
                    token_to_use = hdntl_cookie
                else:
                    token_to_use = extract_hdntl_from_url(url) or ""

                if logo_url:
                    f.write(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title}" tvg-logo="{logo_url}" group-title="{title}", {channel_label} @rtxcric\n')
                else:
                    f.write(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title}" group-title="{title}", {channel_label} @rtxcric\n')

                if not skip_http_headers:
                    _exthttp = f'{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}"'
                    if token_to_use and not force_no_cookie:
                        _exthttp += f',"Cookie":"hdntl={token_to_use}"'
                    _exthttp += '}'
                    f.write(f'#EXTHTTP:{_exthttp}\n')
                    f.write(f'#EXTVLCOPT:http-extra-headers=Origin: {M3U_ORIGIN}\n')
                    f.write(f'#EXTVLCOPT:http-referrer={M3U_REFERER}\n')
                    f.write(f'#EXTVLCOPT:http-user-agent={M3U_USER_AGENT}\n')
                f.write(f"{url}\n")
        print(f"{GREEN}✓ M3U playlist saved as: {filename}{RESET}")
        return True
    except Exception as e:
        print(f"{RED}Failed to create M3U: {e}{RESET}")
        return False

# ===================== CLOUDFLARE WORKERS PUSH =====================

CF_CONFIG_FILE = "fhdcf_config.json"

def load_cf_config():
    try:
        with open(CF_CONFIG_FILE, "r") as f:
            return json.load(f)
    except:
        return None

def save_cf_config(worker_url, api_token):
    with open(CF_CONFIG_FILE, "w") as f:
        json.dump({"worker_url": worker_url, "api_token": api_token}, f)

def _dedupe_m3u_bytes(raw: bytes) -> bytes:
    """Remove true duplicate M3U blocks only.

    Keeps 30M / 30M STABLE / 7M as separate entries (same path is OK).
    Key = full #EXTINF label (after comma) + full stream URL.
    """
    try:
        text_m = raw.decode("utf-8", errors="replace")
    except Exception:
        return raw
    lines = text_m.splitlines(keepends=True)
    out = []
    buf = []
    seen_keys = set()

    def _flush():
        nonlocal buf
        if not buf:
            return
        label = ""
        url_line = ""
        for ln in buf:
            if ln.lstrip().startswith("#EXTINF") and "," in ln:
                label = ln.strip().rsplit(",", 1)[-1].strip()
            s = ln.strip()
            if s and not s.startswith("#"):
                url_line = s.split("|")[0].strip()
                break
        key = f"{label}||{url_line}"
        if key in seen_keys:
            buf = []
            return
        if label or url_line:
            seen_keys.add(key)
        out.extend(buf)
        buf = []

    for ln in lines:
        if ln.startswith("#EXTINF"):
            _flush()
            buf = [ln]
        elif buf:
            buf.append(ln)
            if ln.strip() and not ln.strip().startswith("#"):
                _flush()
        else:
            out.append(ln)
    _flush()
    return "".join(out).encode("utf-8")




def push_to_cloudflare(filename: str, worker_url: str, api_token: str, retries: int = 3) -> bool:
    """Upload M3U via POST multipart/form-data (curl -F file=@... equivalent).

    curl -X POST https://your.workers.dev/upload \
      -H "X-Auth-Token: ..." \
      -F "file=@fhd_auto.m3u"
    """
    import urllib.error
    try:
        with open(filename, "rb") as f:
            file_content = f.read()
    except Exception as e:
        print(f"{RED}Failed to read M3U file: {e}{RESET}")
        return False

    # Drop duplicate stream URL blocks before upload
    try:
        deduped = _dedupe_m3u_bytes(file_content)
        if len(deduped) < len(file_content):
            print(f"  {GRAY}· CF pre-upload: removed duplicate blocks "
                  f"({len(file_content)-len(deduped)} bytes){RESET}")
            file_content = deduped
            try:
                with open(filename, "wb") as f:
                    f.write(file_content)
            except Exception:
                pass
    except Exception:
        pass

    basename = os.path.basename(filename)
    boundary = f"----WebKitFormBoundary{uuid.uuid4().hex[:16]}"

    # multipart/form-data body: field name "file"
    body_parts = []
    body_parts.append(f"--{boundary}\r\n".encode())
    body_parts.append(
        f'Content-Disposition: form-data; name="file"; filename="{basename}"\r\n'.encode()
    )
    body_parts.append(b"Content-Type: application/octet-stream\r\n\r\n")
    body_parts.append(file_content)
    body_parts.append(f"\r\n--{boundary}--\r\n".encode())
    body_data = b"".join(body_parts)

    # cache-bust query so worker/CDN does not stick on stale "Cache Only"
    sep = "&" if "?" in (worker_url or "") else "?"
    upload_url = f"{worker_url}{sep}t={int(time.time())}&size={len(file_content)}"

    for attempt in range(1, retries + 1):
        try:
            headers = {
                "X-Auth-Token": api_token,
                "Content-Type": f"multipart/form-data; boundary={boundary}",
                "Content-Length": str(len(body_data)),
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                "Cache-Control": "no-cache, no-store",
                "Pragma": "no-cache",
                "X-Upload-Force": "1",
            }
            req = request.Request(upload_url, data=body_data, headers=headers, method="POST")
            try:
                with request.urlopen(req, timeout=30) as resp:
                    status = getattr(resp, "status", 200)
                    resp_body = resp.read().decode("utf-8", errors="replace").strip()
                    if status in (200, 201, 204):
                        print(f"{GREEN}✓ Pushed to Cloudflare (POST multipart, attempt {attempt}){RESET}")
                        if resp_body:
                            print(f"{CYAN}  CF: {resp_body[:200]}{RESET}")
                        return True
                    else:
                        print(f"{RED}✗ Cloudflare returned HTTP {status} (attempt {attempt}){RESET}")
                        if resp_body:
                            print(f"{YELLOW}  CF Response: {resp_body[:300]}{RESET}")
            except urllib.error.HTTPError as e:
                err_body = e.read().decode("utf-8", errors="replace").strip()
                print(f"{RED}✗ Cloudflare HTTP {e.code} error (attempt {attempt}): {e.reason}{RESET}")
                if err_body:
                    print(f"{YELLOW}  CF Error: {err_body[:300]}{RESET}")
                if e.code in (401, 403):
                    print(f"{RED}  → Check X-Auth-Token (api_token) value{RESET}")
                    return False
            except urllib.error.URLError as e:
                print(f"{RED}✗ Network error (attempt {attempt}): {e.reason}{RESET}")
        except Exception as e:
            print(f"{RED}✗ Cloudflare push attempt {attempt}/{retries} failed: {e}{RESET}")
        if attempt < retries:
            print(f"{YELLOW}  Retrying in 3 seconds...{RESET}")
            time.sleep(3)
    print(f"{RED}✗ All {retries} Cloudflare push attempts failed.{RESET}")
    return False

# ===================== GIT PUSH =====================

def git_push_m3u(filename: str, message: str = "Auto update M3U playlist") -> bool:
    if subprocess.run(["git", "--version"], capture_output=True).returncode != 0:
        print(f"{YELLOW}⚠ Git not installed. Skipping push.{RESET}")
        return False
    if not os.path.isdir(".git"):
        print(f"{YELLOW}⚠ Not a git repository. Skipping push.{RESET}")
        return False
    try:
        subprocess.run(["git", "add", filename], check=True, capture_output=True)
        has_changes = subprocess.run(
            ["git", "diff", "--cached", "--quiet"], capture_output=True
        ).returncode != 0
        if not has_changes:
            print(f"{YELLOW}⚠ No changes to commit for {filename}. Skipping push.{RESET}")
            return True
        subprocess.run(["git", "commit", "-m", message], check=True, capture_output=True)
        print(f"{GREEN}✓ Committed changes for {filename}{RESET}")
        pull_result = subprocess.run(
            ["git", "pull", "origin", "main", "--no-rebase"],
            capture_output=True, text=True
        )
        if pull_result.returncode != 0:
            subprocess.run(["git", "merge", "--abort"], capture_output=True)
            subprocess.run(["git", "rebase", "--abort"], capture_output=True)
            return False
        subprocess.run(["git", "push"], check=True, capture_output=True)
        print(f"{GREEN}✓ Pushed to GitHub successfully{RESET}")
        return True
    except subprocess.CalledProcessError as e:
        if "push" in str(e.cmd) and e.returncode != 0:
            try:
                subprocess.run(["git", "push", "--force-with-lease"], check=True, capture_output=True)
                print(f"{GREEN}✓ Force-pushed to GitHub successfully{RESET}")
                return True
            except:
                print(f"{RED}Git push failed: {e}{RESET}")
        else:
            print(f"{RED}Git operation failed: {e}{RESET}")
        return False

# ===================== LIVE EVENTS FETCHER =====================

def _extract_title_lines(data: dict, fallback: str = "", alternate: dict = None) -> tuple:
    """Return the two-line title using Hotstar's line1/line2 fields and fallbacks."""
    if not isinstance(data, dict):
        return fallback.strip(), fallback.strip()
    alternate = alternate if isinstance(alternate, dict) else {}
    line1 = str(
        data.get("title_line1") or data.get("line1") or
        data.get("sportsSeasonName") or data.get("show_name") or
        data.get("series_name") or alternate.get("title_line1") or
        alternate.get("line1") or alternate.get("sportsSeasonName") or
        alternate.get("show_name") or alternate.get("series_name") or ""
    ).replace("'", "").strip()
    line2 = str(
        data.get("title_line2") or data.get("line2") or
        alternate.get("title_line2") or alternate.get("line2") or ""
    ).replace("'", "").strip()
    if line1 and line2:
        return line1, line2
    title = str(
        data.get("title") or data.get("name") or
        alternate.get("title") or alternate.get("name") or fallback or ""
    ).replace("'", "").strip()
    if not line1:
        line1 = title
    if not line2:
        line2 = title
    return line1, line2

def _extract_item_logo_h(item: dict) -> str:
    """Extract -h (horizontal) logo ONLY from card.data.image.src.

    HAR/JSON verified: HorizontalContentCard data.image.src = ...-h
    Skip: title_cutout (-t), expanded_content_poster.image (-i), cast_image (-b).
    """
    if not isinstance(item, dict):
        return ""
    for card_key in ("horizontal_content_card", "vertical_content_card",
                     "content_card", "card"):
        card = item.get(card_key)
        if not isinstance(card, dict):
            continue
        d = card.get("data") or card
        # ✅ PRIORITY 1: image.src (this is the -h asset)
        img = d.get("image")
        if isinstance(img, dict):
            src = str(img.get("src") or "").strip()
            if src and _is_h_logo_path(src):
                return _hq_logo(src)
            # If same path has -i/-t variant, try sibling -h
            if src and "cms/prod" in src:
                m = re.match(r"(sources/r\d+/cms/prod/\d+/)(\d+)-[a-z]", src)
                if m:
                    return _hq_logo(f"{m.group(1)}{m.group(2)}-h")
        # ✅ PRIORITY 2: legacy images.h dict
        images = d.get("images")
        if isinstance(images, dict):
            h = str(images.get("h") or "").strip()
            if h:
                return _hq_logo(h)
    # ✅ Fallback: deep-find any -h in raw item JSON
    try:
        raw = json.dumps(item)
        for hit in re.findall(r'(sources/r\d+/cms/prod/\d+/\d+-h)', raw):
            return _hq_logo(hit)
    except Exception:
        pass
    return ""
    
def _extract_title_and_slug(item: dict) -> tuple:
    """Returns (title_line1, title_line2, slug, logo_h). logo_h is '' or full URL."""
    if not isinstance(item, dict):
        return "", "", "", ""
    item_logo = _extract_item_logo_h(item)
    for card_key in ("horizontal_content_card", "vertical_content_card",
                     "content_card", "card"):
        card = item.get(card_key)
        if not isinstance(card, dict):
            continue
        d = card.get("data") or card
        title = ""
        title_line1 = ""
        title_line2 = ""
        title_line1, title_line2 = _extract_title_lines(d, alternate=item)
        for fk in ("footer", "header", "body"):
            fnode = d.get(fk)
            if isinstance(fnode, dict):
                title = (fnode.get("title") or fnode.get("subtitle") or
                         fnode.get("name") or "")
                if title:
                    break
        if not title:
            title = (d.get("title") or d.get("name") or "")
        slug = ""
        actions = d.get("actions") or {}
        for action in (actions.get("on_click") or []):
            nav = action.get("page_navigation") or {}
            if nav.get("page_slug"):
                slug = nav["page_slug"]
                break
        if not slug:
            slug = (d.get("web_url") or d.get("deeplink_url") or
                    d.get("share_url") or d.get("slug") or "")
        if title and slug:
            if not title_line1 or not title_line2:
                title_line1, title_line2 = _extract_title_lines(d, title)
            return title_line1, title_line2, slug, item_logo
    title = (item.get("title") or item.get("name") or
             item.get("show_name") or item.get("series_name") or "")
    if not title:
        b = item.get("body") or {}
        title = (b.get("title") or b.get("name") or "") if isinstance(b, dict) else ""
    slug = (item.get("web_url") or item.get("slug") or
            item.get("share_url") or item.get("deeplink_url") or "")
    if not slug:
        b = item.get("body") or {}
        slug = (b.get("web_url") or b.get("slug") or "") if isinstance(b, dict) else ""
    title_line1, title_line2 = _extract_title_lines(item, title)
    return title_line1, title_line2, slug, item_logo

def _collect_events_from_spaces(spaces: dict) -> list:
    """Walk ALL spaces → collect (title1, title2, url, logo_h) tuples."""
    seen: set = set()
    events: list = []
    ITEM_KEYS = ("items", "cards", "assets", "tray", "content", "data")
    for space_name, space in spaces.items():
        if not isinstance(space, dict):
            continue
        for wrapper in (space.get("widget_wrappers") or []):
            if not isinstance(wrapper, dict):
                continue
            w_data = (wrapper.get("widget") or {}).get("data") or {}
            candidates: list = []
            for k in ITEM_KEYS:
                v = w_data.get(k)
                if isinstance(v, list):
                    candidates.extend(v)
                elif isinstance(v, dict):
                    for kk in ITEM_KEYS:
                        sub = v.get(kk)
                        if isinstance(sub, list):
                            candidates.extend(sub)
            for item in candidates:
                title_line1, title_line2, slug, logo_h = _extract_title_and_slug(item)
                if not title_line1 or not title_line2 or not slug:
                    continue
                dedup_key = slug
                if dedup_key in seen:
                    continue
                seen.add(dedup_key)
                if slug.startswith("http"):
                    url = slug
                elif slug.startswith("/"):
                    url = f"https://www.hotstar.com{slug}"
                else:
                    url = f"https://www.hotstar.com/in/{slug}"
                events.append((title_line1, title_line2, url, logo_h))
    return events

def fetch_live_events(debug: bool = False) -> tuple:
    """Fetch currently live events from the Hotstar live-now editorial page."""
    events: list = []
    token = load_user_token()
    hdrs = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en",
        "X-HS-Platform": "androidtv",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "x-hs-app": "260510002",
        "x-hs-retry-count": "0",
        "x-hs-is-retry": "false",
        "X-HS-Client": (
            "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
            "app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690"
        ),
        "Referer": "https://www.hotstar.com/in/browse/editorial/live-now/1271392364",
        "Origin": "https://www.hotstar.com",
        "Pragma": "no-cache",
        "Cache-Control": "no-cache",
    }
    if token:
        hdrs["x-hs-usertoken"] = token
    live_url = (
        _LIVE_SLUGS_API
        + "?client_capabilities=" + parse.quote(_LIVE_CAPABILITIES)
        + "&drm_parameters=" + parse.quote(_LIVE_DRM)
        + "&request_features=consent_supported"
        + "&lang=eng"
    )
    _last_err = ""
    try:
        req = request.Request(live_url, headers=hdrs, method="GET")
        with request.urlopen(req, timeout=15) as resp:
            body_bytes = resp.read()
        try:
            data = json.loads(body_bytes.decode("utf-8", errors="replace"))
        except Exception as je:
            return events, f"json:{je}"
        spaces = (data.get("success") or {}).get("page", {}).get("spaces", {})
        events = _collect_events_from_spaces(spaces)
    except Exception as exc:
        _last_err = str(exc)
        return events, _last_err
    return events, ""


def _is_true_live_slug(slug: str) -> bool:
    """Only real live watch pages — not movies/titles that merely contain 'live'."""
    s = (slug or "").lower().split("?")[0]
    if not s:
        return False
    if "/video/highlights" in s or "/highlights/" in s:
        return False
    # true live endpoints (24/7 channels + sports live)
    if s.endswith("/live/watch") or "/video/live/watch" in s or "/live/watch" in s:
        return True
    if "/live/watch" in s:
        return True
    return False


def _is_live_episode_slug(slug: str) -> bool:
    """Bigg Boss day-episode etc: /in/shows/.../{contentId}/watch (not /live/watch)."""
    s = (slug or "").lower().split("?")[0]
    if not s or "/shows/" not in s:
        return False
    if "/live/watch" in s:
        return False
    if "/video/highlights" in s or "/highlights/" in s:
        return False
    # .../shows/bigg-boss/1971.../episode-slug/1271696739/watch
    return bool(re.search(r"/shows/.+/\d{6,}/watch$", s))


def fetch_live_from_search(query: str = "Live") -> tuple:
    """
    HAR-verified: BFF search page returns sport_live + show_live + news/tv live.
    Only keep items with /live/watch (exclude movies/highlights).
    Returns (list of (title1, title2, url), error).
    """
    events = []
    seen = set()
    token = load_user_token()
    hdrs = {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en-IN,en;q=0.9",
        "X-HS-Platform": "web",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "X-HS-Client": (
            "platform:web;app_version:26.08.19.1;browser:Chrome;"
            "schema_version:0.0.1797;os:Linux;os_version:x86_64;browser_version:140;network_data:4g"
        ),
        "Referer": f"https://www.hotstar.com/in/explore?search_query={parse.quote(query)}",
        "Origin": "https://www.hotstar.com",
        "Pragma": "no-cache",
        "Cache-Control": "no-cache",
    }
    if token:
        hdrs["x-hs-usertoken"] = token
        hdrs["x-hs-usertoken"] = token

    urls = [
        (
            "https://www.hotstar.com/api/internal/bff/v2/pages/search"
            f"?search_query={parse.quote(query)}&slug=in&slug=explore"
            "&client_capabilities=" + parse.quote(_LIVE_CAPABILITIES)
            + "&drm_parameters=" + parse.quote(_LIVE_DRM)
            + "&request_features=consent_supported&lang=eng"
        ),
        (
            "https://www.hotstar.com/api/internal/bff/v2/slugs/in/explore"
            f"?search_query={parse.quote(query)}"
            "&client_capabilities=" + parse.quote(_LIVE_CAPABILITIES)
            + "&drm_parameters=" + parse.quote(_LIVE_DRM)
            + "&request_features=consent_supported&lang=eng"
        ),
    ]
    err = ""
    for api_url in urls:
        try:
            req = request.Request(api_url, headers=hdrs, method="GET")
            with request.urlopen(req, timeout=15) as resp:
                data = json.loads(resp.read().decode("utf-8", errors="replace"))
            spaces = (data.get("success") or {}).get("page", {}).get("spaces", {})
            if not spaces and isinstance(data.get("success"), dict):
                # alternate shape
                spaces = data.get("success") or {}
            for ev in _collect_events_from_spaces(spaces if isinstance(spaces, dict) else {}):
                t1, t2, url = ev[:3]
                slug = url.replace("https://www.hotstar.com", "")
                is_live = _is_true_live_slug(slug) or _is_true_live_slug(url)
                # episodes come only from fetch_live_episodes_tray (strict BB live filter)
                if not is_live:
                    continue
                key = url.split("?")[0]
                if key in seen:
                    continue
                seen.add(key)
                events.append((t1, t2, url.split("?")[0]))
            # also deep-scan JSON text for page_slug live/watch + live episodes
            raw = json.dumps(data)
            for m in re.finditer(
                r'"page_slug"\s*:\s*"(/in/(?:shows|tv|news|sports|channels)/[^"]+(?:/live)?/watch[^"]*)"',
                raw,
            ):
                slug = m.group(1).split("?")[0]
                is_24_7 = _is_true_live_slug(slug)
                is_ep = _is_live_episode_slug(slug)
                if not is_24_7 and not is_ep:
                    continue
                url = "https://www.hotstar.com" + slug
                if url in seen:
                    continue
                start = max(0, m.start() - 500)
                chunk = raw[start : m.start()]
                titles = re.findall(r'"title"\s*:\s*"([^"]{2,120})"', chunk)
                t2 = titles[-1] if titles else slug.strip("/").split("/")[-2]
                if is_ep and not is_24_7:
                    # episodes ONLY from dedicated tray fetcher — skip noisy search hits
                    continue
                seen.add(url)
                t1 = "LIVE SHOW"
                if "/sports/" in slug:
                    t1 = "LIVE SPORTS"
                elif "/news/" in slug:
                    t1 = "LIVE NEWS"
                elif "/tv/" in slug:
                    t1 = "LIVE TV"
                elif "/shows/" in slug:
                    t1 = "LIVE SHOW"
                events.append((t1, t2.replace("-", " ").title(), url))
            if events:
                break
        except Exception as e:
            err = str(e)
            continue
    return events, err


def fetch_live_episodes_tray() -> tuple:
    """
    ONLY true live Bigg Boss day-episodes (isLive + BB Day title).
    HAR tray: reco-editorial/enter-the-bigg-boss-house
    Rejects VOD dramas / numeric-only titles / non-live show pages.
    """
    events = []
    seen = set()
    token = load_user_token()
    hdrs = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Accept": "application/json, text/plain, */*",
        "X-HS-Platform": "androidtv",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "x-hs-app": "260510002",
        "X-HS-Client": (
            "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
            "app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690"
        ),
        "Referer": "https://www.hotstar.com/in/",
        "Origin": "https://www.hotstar.com",
        "Pragma": "no-cache",
        "Cache-Control": "no-cache",
    }
    if token:
        hdrs["x-hs-usertoken"] = token

    tray_slugs = [
        "in/browse/reco-editorial/enter-the-bigg-boss-house/tp-ed_CNKjst4EEAEaAQEwATgA",
        "in/shows/bigg-boss/1971002586",
        "in/shows/bigg-boss-tamil/1260140124",
        "in/shows/bigg-boss-telugu/1260140125",
        "in/shows/bigg-boss-kannada/1260028094",
        "in/shows/bigg-boss-malayalam/1260028093",
    ]

    def _is_bb_live_title(title: str) -> bool:
        t = (title or "").strip()
        if not t or re.fullmatch(r"\d{6,}", t):
            return False
        tl = t.lower()
        # reject clear VOD / drama / non-BB
        if re.search(
            r"(saza|shikar|sherni|bali|balidaan|khabri|aarya|unfit mother|"
            r"panje|waqt aa gaya|galti ki|clip|highlight|promo|trailer)",
            tl,
        ):
            return False
        # must look like Bigg Boss regional day episode / premiere
        bb = bool(re.search(
            r"\b(bbhin|bbtam|bbtel|bbkan|bbmal|bbban|bbs\d*|bb\s*hin|bb\s*tam|"
            r"bigg\s*boss|bb\s*day)\b",
            tl,
        ))
        day = bool(re.search(
            r"\b(day\s*\d+|grand\s*premiere|nomination|housemates?|"
            r"leader|power\s*drop|vardaan|toofan)\b",
            tl,
        ))
        return bb and day

    def _ctx_is_live(ctx: str) -> bool:
        c = (ctx or "").lower()
        return any(x in c for x in (
            '"islive":true', '"is_live":true', '"live":true',
            '"islive": true', '"is_live": true', '"live": true',
            '"content_type":"episode_live"', '"contenttype":"episode_live"',
            '"content_type":"show_live"', 'show_live', 'episode_live',
        ))

    def _add(t2, url):
        u = (url or "").split("?")[0]
        if not u or u in seen:
            return
        if not _is_bb_live_title(t2):
            return
        seen.add(u)
        events.append(("LIVE EPISODE", t2, u))

    def _scan_raw(raw: str):
        # page_slug episode watch under /shows/
        for m in re.finditer(
            r'"page_slug"\s*:\s*"(/in/shows/[^"]+/\d{6,}/watch[^"]*)"',
            raw,
        ):
            slug = m.group(1).split("?")[0]
            if "/live/watch" in slug:
                continue
            url = "https://www.hotstar.com" + slug
            ctx0 = max(0, m.start() - 800)
            ctx1 = min(len(raw), m.end() + 300)
            ctx = raw[ctx0:ctx1]
            # STRICT: must be marked live in nearby JSON
            if not _ctx_is_live(ctx):
                continue
            titles = re.findall(r'"title"\s*:\s*"([^"]{3,120})"', ctx)
            t2 = titles[-1] if titles else ""
            if not t2:
                # slug segment before content id
                parts = [p for p in slug.strip("/").split("/") if p]
                t2 = parts[-2].replace("-", " ") if len(parts) >= 2 else ""
            _add(t2, url)

    err = ""
    for slug in tray_slugs:
        api = (
            f"https://www.hotstar.com/api/internal/bff/v2/slugs/{slug}"
            f"?client_capabilities={parse.quote(_LIVE_CAPABILITIES)}"
            f"&drm_parameters={parse.quote(_LIVE_DRM)}"
            f"&request_features=consent_supported&lang=eng"
        )
        try:
            req = request.Request(api, headers=hdrs, method="GET")
            with request.urlopen(req, timeout=18) as resp:
                body = resp.read()
            try:
                import gzip as _gz
                if body[:2] == b"\x1f\x8b":
                    body = _gz.decompress(body)
            except Exception:
                pass
            text_body = body.decode("utf-8", errors="replace")
            if text_body.lstrip().startswith("<"):
                continue
            _scan_raw(text_body)
        except Exception as e:
            err = str(e)
            continue

    return events, (err if not events else "")



def fetch_all_live() -> tuple:
    """
    Merge:
      1) best-in-sports LIVE (sport_live)
      2) live-now editorial
      3) search Live → show_live / news / tv live (HAR)
    Only true /live/watch items. Dedup by URL.
    """
    merged = []
    seen = set()
    errors = []

    for fetcher, label in [
        (lambda: fetch_best_in_sports("LIVE"), "sports"),
        (lambda: fetch_live_events(), "live-now"),
        (lambda: fetch_live_from_search("Live"), "search"),
        (lambda: fetch_live_from_search("live show"), "search-show"),
        (lambda: fetch_live_from_search("khatron"), "search-kkk"),
        (lambda: fetch_live_from_search("bigg boss"), "search-bb"),
        (lambda: fetch_live_from_search("bigg boss live"), "search-bb-live"),
        (lambda: fetch_live_from_search("bbhin"), "search-bbhin"),
        (lambda: fetch_live_episodes_tray(), "bb-episodes"),
    ]:
        try:
            evs, err = fetcher()
            if err:
                errors.append(f"{label}:{err}")
            for ev in evs or []:
                t1, t2, u = ev[:3]
                u = (u or "").split("?")[0]
                _logo = ev[3] if len(ev) > 3 else ""
                if not u:
                    continue
                # keep only live watch URLs when from search; sports already filtered
                if label.startswith("search") and not _is_true_live_slug(u):
                    continue
                # DROP live news + linear LIVE TV — keep sports + LIVE SHOW + LIVE EPISODE
                t1u = (t1 or "").upper()
                t2u = (t2 or "").upper()
                uu = u.lower()
                if "LIVE EPISODE" in t1u or _is_live_episode_slug(uu):
                    pass  # always keep
                elif "LIVE NEWS" in t1u or "/news/" in uu:
                    continue
                elif "NEWS18" in t2u or "CNBC" in t2u or "CNN NEWS" in t2u:
                    continue
                elif "LIVE TV" in t1u or (uu.find("/tv/") >= 0 and "/shows/" not in uu):
                    continue
                key = u
                if key in seen:
                    continue
                seen.add(key)
                merged.append((t1, t2, u, _logo))
        except Exception as e:
            errors.append(f"{label}:{e}")

    return merged, ("; ".join(errors) if errors and not merged else "")

# ===================== SPORTS EVENTS FETCHER =====================

def _collect_sports_from_spaces(spaces: dict, content_filter: str = "ALL") -> list:
    """
    Walk spaces and collect (title, url) based on content_filter:
      "LIVE"       — only live streams
      "HIGHLIGHTS" — only highlights/clips
      "OTHER"      — everything except live and highlights
      "ALL"        — everything
    """
    seen: set = set()
    events: list = []
    ITEM_KEYS = ("items", "cards", "assets", "tray", "content", "data")
    LIVE_TYPES = {"LIVE", "LIVE_TV", "LIVETV", "SPORT_LIVE", "SHOW_LIVE", "EPISODE_LIVE", "CHANNEL_LIVE"}
    HIGHLIGHT_TYPES = {"HIGHLIGHT", "HIGHLIGHTS", "CLIP", "CLIPS", "SHORTS"}

    def _detect_ctype(d: dict) -> str:
        for ct_key in ("content_type", "asset_type", "type", "content_sub_type"):
            ct = d.get(ct_key) or ""
            if ct:
                return str(ct).upper()
        badge = d.get("badge") or {}
        if isinstance(badge, dict):
            badge_text = (badge.get("text") or badge.get("label") or "").upper()
            if "LIVE" in badge_text:
                return "LIVE"
        return ""

    def _extract_title_slug_type(item: dict) -> tuple:
        if not isinstance(item, dict):
            return "", "", ""
        content_type = ""
        for card_key in ("horizontal_content_card", "vertical_content_card",
                         "content_card", "card"):
            card = item.get(card_key)
            if not isinstance(card, dict):
                continue
            d = card.get("data") or card
            title = ""
            title_line1 = ""
            title_line2 = ""
            for fk in ("footer", "header", "body"):
                fnode = d.get(fk)
                if isinstance(fnode, dict):
                    title = (fnode.get("title") or fnode.get("subtitle") or
                             fnode.get("name") or "")
                    if title:
                        break
            if not title:
                title = (d.get("title") or d.get("name") or "")
            title_line1, title_line2 = _extract_title_lines(d, title, alternate=item)
            content_type = _detect_ctype(d)
            slug = ""
            actions = d.get("actions") or {}
            for action in (actions.get("on_click") or []):
                nav = action.get("page_navigation") or {}
                if nav.get("page_slug"):
                    slug = nav["page_slug"]
                    break
            if not slug:
                slug = (d.get("web_url") or d.get("deeplink_url") or
                        d.get("share_url") or d.get("slug") or "")
            if title and slug:
                return title_line1, title_line2, slug, content_type
        title = (item.get("title") or item.get("name") or
                 item.get("show_name") or item.get("series_name") or "")
        if not title:
            b = item.get("body") or {}
            title = (b.get("title") or b.get("name") or "") if isinstance(b, dict) else ""
        content_type = _detect_ctype(item)
        slug = (item.get("web_url") or item.get("slug") or
                item.get("share_url") or item.get("deeplink_url") or "")
        if not slug:
            b = item.get("body") or {}
            slug = (b.get("web_url") or b.get("slug") or "") if isinstance(b, dict) else ""
        title_line1, title_line2 = _extract_title_lines(item, title)
        return title_line1, title_line2, slug, content_type

    for space_name, space in spaces.items():
        if not isinstance(space, dict):
            continue
        for wrapper in (space.get("widget_wrappers") or []):
            if not isinstance(wrapper, dict):
                continue
            w_data = (wrapper.get("widget") or {}).get("data") or {}
            candidates: list = []
            for k in ITEM_KEYS:
                v = w_data.get(k)
                if isinstance(v, list):
                    candidates.extend(v)
                elif isinstance(v, dict):
                    for kk in ITEM_KEYS:
                        sub = v.get(kk)
                        if isinstance(sub, list):
                            candidates.extend(sub)
            for item in candidates:
                title_line1, title_line2, slug, ctype = _extract_title_slug_type(item)
                if not title_line1 or not title_line2 or not slug:
                    continue
                is_live = (
                    ctype in LIVE_TYPES or
                    "LIVE" in ctype or
                    "/live/" in slug.lower()
                )
                is_highlight = (
                    ctype in HIGHLIGHT_TYPES or
                    "HIGHLIGHT" in ctype or
                    "CLIP" in ctype or
                    "/highlights/" in slug.lower() or
                    "/clip" in slug.lower()
                )
                if content_filter == "LIVE" and not is_live:
                    continue
                elif content_filter == "HIGHLIGHTS" and not is_highlight:
                    continue
                elif content_filter == "OTHER" and (is_live or is_highlight):
                    continue
                dedup_key = slug
                if dedup_key in seen:
                    continue
                seen.add(dedup_key)
                if slug.startswith("http"):
                    url = slug
                elif slug.startswith("/"):
                    url = f"https://www.hotstar.com{slug}"
                else:
                    url = f"https://www.hotstar.com/in/{slug}"
                events.append((title_line1, title_line2, url))
    return events


def _normalize_event_title(value: str) -> str:
    """Normalize titles enough to match the legacy and current Hotstar APIs."""
    return re.sub(r"[^a-z0-9]+", " ", str(value or "").lower()).strip()


# Cache for hotlive.php-style legacy logos (images.h only — never images.b)
_LEGACY_LOGO_CACHE = {"fetched_at": 0.0, "by_title": {}, "by_id": {}}
_LEGACY_LOGO_TTL = 120  # same 2-min cache as PHP hotlive.json


def _php_style_logo(image_h_path: str) -> str:
    """Full-quality horizontal logo — no f_auto/t_web transform (higher res).
    https://img1.hotstarext.com/image/upload/sources/r1/cms/prod/.../...-h
    """
    p = (image_h_path or "").strip()
    if not p:
        return ""
    if p.startswith("http"):
        if "/image/upload/" in p:
            rest = p.split("/image/upload/", 1)[1]
            # strip any transform segment (f_auto..., t_web..., q_...)
            if rest.startswith("f_") or rest.startswith("t_") or rest.startswith("q_"):
                rest = rest.split("/", 1)[-1] if "/" in rest else rest
            return f"https://img1.hotstarext.com/image/upload/{rest.lstrip('/')}"
        return p
    return f"https://img1.hotstarext.com/image/upload/{p.lstrip('/')}"


def _fetch_legacy_title_lines() -> dict:
    """Same APIs + logo logic as hotlive.php — ONLY item['images']['h']."""
    global _LEGACY_LOGO_CACHE
    now = time.time()
    if (
        _LEGACY_LOGO_CACHE.get("by_title")
        and (now - float(_LEGACY_LOGO_CACHE.get("fetched_at") or 0)) < _LEGACY_LOGO_TTL
    ):
        return _LEGACY_LOGO_CACHE["by_title"]

    urls = (
        "https://api.hotstar.com/o/v1/page/1984?offset=0&size=20&tao=0&tas=20",
        "https://api.hotstar.com/o/v1/page/2420?offset=0&size=20&tao=0&tas=20",
    )
    headers = {
        "x-country-code": "IN",
        "x-platform-code": "PCTV",
        "User-Agent": "Mozilla/5.0",
        "Accept": "application/json",
    }
    title_map = {}
    id_map = {}
    for api_url in urls:
        try:
            req = request.Request(api_url, headers=headers, method="GET")
            # legacy API often fails via India proxy — try direct
            try:
                with _direct_urlopen(req, timeout=15) as resp:
                    payload = json.loads(resp.read().decode("utf-8", errors="replace"))
            except Exception:
                with request.urlopen(req, timeout=15) as resp:
                    payload = json.loads(resp.read().decode("utf-8", errors="replace"))
            trays = ((payload.get("body") or {}).get("results") or {}).get("trays") or {}
            items = trays.get("items") or []
            for tray in items:
                assets = tray.get("assets") or {}
                for item in assets.get("items") or []:
                    if str(item.get("live", "")).lower() != "true":
                        continue
                    title_line1 = item.get("line1") or item.get("sportsSeasonName") or ""
                    title_line2 = item.get("line2") or item.get("title") or ""
                    # PHP exact: ONLY images.h — never images.b
                    image_h = ((item.get("images") or {}).get("h") or "").strip()
                    if not image_h:
                        continue
                    logo_url = _php_style_logo(image_h)
                    content_id = str(item.get("contentId") or item.get("content_id") or "").strip()
                    clean_pair = (
                        str(title_line1).replace("'", "").strip(),
                        str(title_line2).replace("'", "").strip(),
                    )
                    if clean_pair[1]:
                        title_map[_normalize_event_title(clean_pair[1])] = (
                            clean_pair[0], clean_pair[1], logo_url
                        )
                        # also index by line1 and full "line1: line2"
                        if clean_pair[0]:
                            title_map[_normalize_event_title(clean_pair[0])] = (
                                clean_pair[0], clean_pair[1], logo_url
                            )
                            title_map[_normalize_event_title(f"{clean_pair[0]} {clean_pair[1]}")] = (
                                clean_pair[0], clean_pair[1], logo_url
                            )
                    if content_id:
                        id_map[content_id] = logo_url
        except Exception:
            continue
    _LEGACY_LOGO_CACHE = {
        "fetched_at": time.time(),
        "by_title": title_map,
        "by_id": id_map,
    }
    return title_map


def lookup_legacy_logo(title1: str = "", title2: str = "", url: str = "") -> str:
    """Resolve PHP-style images.h logo by title or contentId in URL."""
    _fetch_legacy_title_lines()  # refresh cache if needed
    by_title = _LEGACY_LOGO_CACHE.get("by_title") or {}
    by_id = _LEGACY_LOGO_CACHE.get("by_id") or {}
    # contentId from slug path (last long numeric segment)
    if url:
        for seg in re.findall(r"/(\d{5,})(?:/|$)", url):
            if seg in by_id:
                return by_id[seg]
    for key in (
        _normalize_event_title(title2 or ""),
        _normalize_event_title(title1 or ""),
        _normalize_event_title(f"{title1 or ''} {title2 or ''}"),
    ):
        if key and key in by_title:
            pair = by_title[key]
            if pair and len(pair) >= 3 and pair[2]:
                return pair[2]
    # soft match: any title key contained in our title
    t2n = _normalize_event_title(title2 or "")
    t1n = _normalize_event_title(title1 or "")
    for k, pair in by_title.items():
        if not k or not pair or len(pair) < 3:
            continue
        if t2n and (k in t2n or t2n in k):
            return pair[2]
        if t1n and (k in t1n or t1n in k):
            return pair[2]
    return ""


def _fetch_logo_by_content_id(content_id: str) -> str:
    """Fetch images.h (or best image) from Hotstar o/v1 detail for contentId."""
    cid = str(content_id or "").strip()
    if not cid or not cid.isdigit():
        return ""
    # cache on legacy id map
    by_id = (_LEGACY_LOGO_CACHE.get("by_id") or {})
    if cid in by_id and by_id[cid]:
        return by_id[cid]
    headers = {
        "x-country-code": "IN",
        "x-platform-code": "PCTV",
        "User-Agent": "Mozilla/5.0",
        "Accept": "application/json",
    }
    urls = (
        f"https://api.hotstar.com/o/v1/detail?contentId={cid}&offset=0&size=20",
        f"https://api.hotstar.com/o/v1/episode?contentId={cid}&offset=0&size=20",
        f"https://api.hotstar.com/o/v1/sports/match?contentId={cid}",
    )
    for api_url in urls:
        try:
            req = request.Request(api_url, headers=headers, method="GET")
            try:
                with _direct_urlopen(req, timeout=12) as resp:
                    payload = json.loads(resp.read().decode("utf-8", errors="replace"))
            except Exception:
                with request.urlopen(req, timeout=12) as resp:
                    payload = json.loads(resp.read().decode("utf-8", errors="replace"))
            # walk for images.h first
            raw = json.dumps(payload)
            for pat in (
                r'"h"\s*:\s*"(sources/r\d+/cms/prod/\d+/\d+-h)"',
                r'"(?:src|url)"\s*:\s*"(sources/r\d+/cms/prod/\d+/\d+-h)"',
                r'(sources/r\d+/cms/prod/\d+/\d+-h)',
            ):
                hits = re.findall(pat, raw)
                if hits:
                    logo = _php_style_logo(hits[0])
                    if logo:
                        by_id[cid] = logo
                        _LEGACY_LOGO_CACHE["by_id"] = by_id
                        return logo
            # prefer -b over -t from detail
            b_hits = re.findall(r'(sources/r\d+/cms/prod/\d+/\d+-b)', raw)
            if b_hits:
                logo = _php_style_logo(b_hits[0])
                if logo:
                    by_id[cid] = logo
                    _LEGACY_LOGO_CACHE["by_id"] = by_id
                    return logo
        except Exception:
            continue
    return ""


def resolve_event_logo(title1: str = "", title2: str = "", url: str = "", player_logo: str = "") -> str:
    """Best logo: images.h > content detail -h > player -b (cast) > player other. Never prefer -t."""
    # 1) legacy list images.h
    try:
        leg = lookup_legacy_logo(title1, title2, url)
        if leg and _is_h_logo_path(leg):
            return leg
    except Exception:
        leg = ""
    # 2) contentId detail API
    cid = ""
    if url:
        nums = re.findall(r"/(\d{6,})(?:/|$|\?)", url)
        if nums:
            cid = nums[-1] if len(nums[-1]) >= 6 else (nums[0] if nums else "")
            # prefer content id near end (Hotstar content ids are 10 digits often)
            for n in reversed(nums):
                if len(n) >= 9:
                    cid = n
                    break
    if cid:
        try:
            dlogo = _fetch_logo_by_content_id(cid)
            if dlogo and (_is_h_logo_path(dlogo) or not leg):
                if _is_h_logo_path(dlogo) or not (player_logo and _is_h_logo_path(player_logo)):
                    if _is_h_logo_path(dlogo):
                        return dlogo
                    if not leg:
                        leg = dlogo
        except Exception:
            pass
    # 3) player_config / watch API logo — prefer -b (cast_image) over -t (title_cutout)
    pl = player_logo or ""
    if pl and _is_h_logo_path(pl):
        return pl
    if leg:
        return leg
    if pl and _logo_asset_suffix(pl) == "b":
        return _hq_logo(pl)
    if pl and not _is_bad_logo_path(pl):
        return _hq_logo(pl)
    if pl and _logo_asset_suffix(pl) == "b":
        return _hq_logo(pl)
    # 4) last resort: cast_image -b style path is better than empty
    if pl:
        # skip pure -t if possible
        if _logo_asset_suffix(pl) != "t":
            return _hq_logo(pl)
    return _hq_logo(pl) if pl else ""


def _apply_legacy_title_lines(events: list) -> list:
    """Preserve API -h logo (best); fall back to legacy images.h only if missing."""
    if not events:
        return events
    title_map = _fetch_legacy_title_lines()
    updated = []
    for event in events:
        if len(event) >= 4:
            title_line1, title_line2, event_url, logo_url = event[0], event[1], event[2], event[3]
        elif len(event) == 3:
            title_line1, title_line2, event_url = event
            logo_url = ""
        else:
            updated.append(event)
            continue
        pair = title_map.get(_normalize_event_title(title_line2))
        if pair:
            title_line1, title_line2 = pair[0], pair[1]
            pair_logo = pair[2] if len(pair) > 2 else ""
            # ✅ Never downgrade an existing -h with a legacy -b/-t
            if logo_url and _is_h_logo_path(logo_url):
                pass  # keep API -h
            elif pair_logo and _is_h_logo_path(pair_logo):
                logo_url = pair_logo
            elif not logo_url:
                logo_url = pair_logo
        if not logo_url or not _is_h_logo_path(logo_url):
            leg = lookup_legacy_logo(title_line1, title_line2, event_url)
            if leg and _is_h_logo_path(leg):
                logo_url = leg
        updated.append((title_line1, title_line2, event_url, logo_url))
    return updated


def fetch_best_in_sports(content_filter: str = "ALL") -> tuple:
    """
    Fetch content from Hotstar best-in-sports editorial page.
    content_filter: "LIVE", "HIGHLIGHTS", "OTHER", "ALL"
    Returns (list of (title, url) tuples, error_string).
    """
    events: list = []
    token = load_user_token()
    hdrs = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en",
        "X-HS-Platform": "androidtv",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "x-hs-app": "260510002",
        "x-hs-retry-count": "0",
        "x-hs-is-retry": "false",
        "X-HS-Client": (
            "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
            "app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690"
        ),
        "Referer": "https://www.hotstar.com/in/browse/editorial/best-in-sports/6517",
        "Origin": "https://www.hotstar.com",
        "Pragma": "no-cache",
        "Cache-Control": "no-cache",
    }
    if token:
        hdrs["x-hs-usertoken"] = token
    sports_url_base = (
        _SPORTS_SLUGS_API
        + "?client_capabilities=" + parse.quote(_LIVE_CAPABILITIES)
        + "&drm_parameters=" + parse.quote(_LIVE_DRM)
        + "&request_features=consent_supported"
        + "&lang=eng"
    )
    _BFF_BASE = "https://www.hotstar.com/api/internal/bff"

    def _fetch_more_url(more_url: str) -> tuple:
        full = _BFF_BASE + more_url if more_url.startswith("/") else more_url
        req_m = request.Request(full, headers=hdrs, method="GET")
        with request.urlopen(req_m, timeout=15) as r:
            d = json.loads(r.read().decode("utf-8", errors="replace"))
        payload = d.get("data") or d.get("success") or {}
        items    = payload.get("items") or []
        next_url = payload.get("more_grid_items_url") or ""
        return items, next_url

    def _ingest(items: list, seen: set) -> int:
        fake_spaces = {"pg": {"widget_wrappers": [{"widget": {"data": {"items": items}}}]}}
        added = 0
        for ev in _collect_sports_from_spaces(fake_spaces, content_filter):
            if ev[2] not in seen:
                seen.add(ev[2])
                events.append(ev)
                added += 1
        return added

    try:
        req = request.Request(sports_url_base, headers=hdrs, method="GET")
        with request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="replace"))
        spaces = (data.get("success") or {}).get("page", {}).get("spaces", {})
        events = _collect_sports_from_spaces(spaces, content_filter)
        seen_urls = {ev[2] for ev in events}
        _pages_fetched = 0
        _MAX_PAGES = 20
        for space in spaces.values():
            if not isinstance(space, dict):
                continue
            for wrapper in (space.get("widget_wrappers") or []):
                widget  = wrapper.get("widget") or {}
                w_data  = widget.get("data") or {}
                initial_items_count = len(w_data.get("items") or [])
                more_url = (
                    w_data.get("more_grid_items_url") or
                    widget.get("more_grid_items_url") or
                    wrapper.get("more_grid_items_url") or ""
                )
                widget_id = (
                    widget.get("id") or widget.get("widget_id") or
                    w_data.get("id") or w_data.get("widget_id") or ""
                )
                if not more_url and initial_items_count > 0 and widget_id:
                    more_url = (
                        f"/api/internal/bff/v2/pages/in/browse/editorial"
                        f"/best-in-sports/6517/widgets/{widget_id}/items"
                        f"?size=10&offset={initial_items_count}"
                    )
                offset_for_built_url = initial_items_count + 10
                while more_url and _pages_fetched < _MAX_PAGES:
                    _pages_fetched += 1
                    try:
                        more_items, more_url = _fetch_more_url(more_url)
                        if not more_items:
                            break
                        added = _ingest(more_items, seen_urls)
                        if more_url == "" and widget_id and added > 0:
                            more_url = (
                                f"/api/internal/bff/v2/pages/in/browse/editorial"
                                f"/best-in-sports/6517/widgets/{widget_id}/items"
                                f"?size=10&offset={offset_for_built_url}"
                            )
                            offset_for_built_url += 10
                        if added == 0:
                            break
                    except Exception:
                        break
        if len(events) <= 10 and _pages_fetched == 0:
            offset = 10
            while _pages_fetched < _MAX_PAGES:
                _pages_fetched += 1
                try:
                    fallback_url = sports_url_base + f"&offset={offset}&size=10"
                    req_f = request.Request(fallback_url, headers=hdrs, method="GET")
                    with request.urlopen(req_f, timeout=15) as resp_f:
                        data_f = json.loads(resp_f.read().decode("utf-8", errors="replace"))
                    spaces_f = (data_f.get("success") or {}).get("page", {}).get("spaces", {})
                    if not spaces_f:
                        break
                    added = 0
                    for ev in _collect_sports_from_spaces(spaces_f, content_filter):
                        if ev[2] not in seen_urls:
                            seen_urls.add(ev[2])
                            events.append(ev)
                            added += 1
                    if added == 0:
                        break
                    offset += 10
                except Exception:
                    break
    except Exception as exc:
        return events, str(exc)
    if content_filter == "LIVE":
        events = _apply_legacy_title_lines(events)
    return events, ""


# ===================== FHD HELPER FUNCTIONS =====================

def _init_proxy():
    """Direct connection only (no proxy)."""
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    urllib.request.install_opener(opener)
    print(f"{GREEN}✓ Direct connection (no proxy){RESET}")
    try:
        req = request.Request(
            "https://www.hotstar.com/",
            headers={"User-Agent": "Mozilla/5.0"},
            method="HEAD",
        )
        with request.urlopen(req, timeout=8) as resp:
            print(f"  {GREEN}✓ Network reachable{RESET}")
    except Exception as e:
        print(f"  {YELLOW}⚠ Network check: {str(e)[:100]}{RESET}")


def load_cf_config_fhd():
    """Cloudflare config — hardcoded in script; optional livecf_config.json overrides."""
    # Built-in defaults (same as livecf_config.json)
    cfg = {
        "worker_url": "https://your.workers.dev/upload",
        "api_token": "your_api_token",
    }
    try:
        with open(LIVE_CF_CONFIG, "r") as f:
            disk = json.load(f)
        if isinstance(disk, dict):
            if disk.get("worker_url", "").startswith("http"):
                cfg["worker_url"] = disk["worker_url"]
            if disk.get("api_token"):
                cfg["api_token"] = disk["api_token"]
    except Exception:
        pass
    return cfg


def load_fhd_tokens() -> list:
    """Load every numeric token*.txt file present in FHD_TOKEN_DIR.
    Returns list of (tok_num, tok_str, file_path).

    Priority:
      1. FHD_TOKEN_DIR env var  →  use that folder
      2. <script_dir>/tokens/   →  default folder
      3. <script_dir>/token.txt →  single-token fallback (index 0)
    """
    tok_dir = os.environ.get("FHD_TOKEN_DIR", os.path.join(_SCRIPT_DIR, "tokens"))
    found = []
    token_files = []
    try:
        for name in os.listdir(tok_dir):
            match = re.fullmatch(r"token(\d+)\.txt", name)
            if match:
                token_files.append((int(match.group(1)), name))
    except OSError:
        token_files = []

    for i, name in sorted(token_files):
        tp = os.path.join(tok_dir, name)
        if os.path.isfile(tp):
            try:
                with open(tp, "r", encoding="utf-8") as f:
                    tok = f.read().strip()
                if tok:
                    found.append((i, tok, tp))
            except Exception:
                pass
    # Fallback: token.txt in same directory as this script
    if not found:
        fallback = TOKEN_FILE
        if os.path.isfile(fallback):
            try:
                with open(fallback, "r", encoding="utf-8") as f:
                    tok = f.read().strip()
                if tok:
                    found.append((0, tok, fallback))
            except Exception:
                pass
    return found


def check_token_valid_fast(token: str, slug_path: str = "sports/cricket") -> str:
    """
    p.py-style token check:
      "ok"      → HTTP 200 + body has non-empty "success"
      "bad"     → 401/403 OR success missing/empty
      "unknown" → timeout/network (keep usable, don't cache as ok)
    """
    if not (token or "").strip():
        return "bad"
    try:
        test_url = f"https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug_path}/watch"
        _h = HEADERS_BASE.copy()
        _h["x-hs-usertoken"] = token.strip()
        _h["X-Request-Id"] = str(uuid.uuid4())
        _h["x-hs-request-id"] = str(uuid.uuid4())
        _h["x-hs-device-id"] = str(uuid.uuid4())
        req = request.Request(test_url, headers=_h)
        with request.urlopen(req, timeout=6) as resp:
            body = resp.read(4096)
        try:
            data = json.loads(body)
            if "success" not in data or not data.get("success"):
                return "bad"
        except Exception:
            return "unknown"
        return "ok"
    except Exception as e:
        code = getattr(e, "code", None)
        if code in (401, 403):
            return "bad"
        return "unknown"


_TOKEN_VALID_CACHE_FILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)) or ".",
    ".fhd_token_valid_cache.json",
)
_TOKEN_CACHE_TTL = 1800  # 30 min (same as p.py)


def fast_check_all_tokens(all_tokens: list) -> list:
    """p.py-style parallel check — only cache definitive ok/bad."""
    n = len(all_tokens)
    t0 = time.time()

    cache = {}
    try:
        if os.path.isfile(_TOKEN_VALID_CACHE_FILE):
            with open(_TOKEN_VALID_CACHE_FILE, "r", encoding="utf-8") as f:
                blob = json.load(f)
            if time.time() - float(blob.get("ts") or 0) < _TOKEN_CACHE_TTL:
                cache = blob.get("map") or {}
            else:
                cache = {}
    except Exception:
        cache = {}

    results = {}
    need_check = []
    for tn, ts, path in all_tokens:
        fp = (ts or "")[:64]
        if fp in cache and cache[fp] in ("ok", "bad"):
            results[tn] = cache[fp]
        else:
            need_check.append((tn, ts))

    if need_check:
        print(f"{CYAN}Checking {len(need_check)}/{n} tokens in parallel (cache hit {n - len(need_check)})...{RESET}")
    else:
        print(f"{CYAN}Token cache hit — all {n} tokens...{RESET}")

    def _chk(tok_num, tok_str):
        return tok_num, tok_str, check_token_valid_fast(tok_str)

    if need_check:
        with ThreadPoolExecutor(max_workers=min(max(len(need_check), 1), 40)) as pool:
            futs = {pool.submit(_chk, tn, ts): tn for tn, ts in need_check}
            for f in as_completed(futs):
                try:
                    tn, ts, status = f.result()
                    results[tn] = status
                    if status in ("ok", "bad"):
                        cache[(ts or "")[:64]] = status
                except Exception:
                    results[futs[f]] = "unknown"
        try:
            with open(_TOKEN_VALID_CACHE_FILE, "w", encoding="utf-8") as f:
                json.dump({"ts": time.time(), "map": cache}, f)
        except Exception:
            pass

    elapsed = time.time() - t0
    valid = [t for t in all_tokens if results.get(t[0], "unknown") in ("ok", "unknown")]
    invalid = [t for t in all_tokens if results.get(t[0]) == "bad"]
    n_ok = sum(1 for t in all_tokens if results.get(t[0]) == "ok")
    n_unk = sum(1 for t in all_tokens if results.get(t[0]) == "unknown")
    usable = n_ok + n_unk
    print(f"{GREEN}✓ Valid: {usable}/{n} tokens  ({elapsed:.1f}s){RESET}"
          + (f"  {GRAY}(ok={n_ok}, timeout={n_unk}){RESET}" if n_unk else ""))
    if invalid:
        _names = [f"token{t[0]}.txt" if t[0] else "token.txt" for t in invalid]
        print(f"{RED}  Expired: {', '.join(_names)}{RESET}")
    return valid



# ===================== c.py-style 24H hdntl (DRM MPD + JHS) =====================

def build_jhs_headers_android():
    ua = M3U_USER_AGENT if "M3U_USER_AGENT" in globals() else "Hotstar;in.startv.hotstar/25.02.24.8.11169@rtxcric(Android/15)"
    cs = (
        "platform:android;app_id:in.startv.hotstar;"
        "app_version:25.02.24.8.11169;os:Android;os_version:15;schema_version:0.0.1690"
    )
    h = {
        "User-Agent": ua,
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "eng",
        "Referer": "https://www.hotstar.com/in/explore?search_query=live",
        "Connection": "keep-alive",
        "x-hs-retry-count": "0",
        "X-HS-Platform": "android",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "X-Request-Id": str(uuid.uuid4()),
        "x-hs-device-id": str(uuid.uuid4()),
        "x-hs-is-retry": "false",
        "x-hs-request-id": str(uuid.uuid4()),
        "X-HS-Client": cs,
        "x-hs-app": "250224008",
        "Pragma": "no-cache",
        "Cache-Control": "no-cache",
    }
    token = load_user_token()
    if token:
        h["x-hs-usertoken"] = token
    return h


def build_jhs_api_url(slug_path: str, lang: str, is_live: bool = False):
    if is_live:
        capabilities = {
            "ads": ["ssai"],
            "audio_channel": ["stereo"],
            "container": ["ts"],
            "dvr": ["short"],
            "dynamic_range": ["sdr"],
            "encryption": ["plain"],
            "ladder": ["phone"],
            "package": ["hls"],
            "resolution": ["hd", "fhd"],
            "video_codec": ["h264"],
        }
        drm = {"widevine_security_level": ["SW_SECURE_DECODE"]}
    else:
        capabilities = {
            "ads": ["non_ssai"],
            "audio_channel": ["stereo"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short"],
            "dynamic_range": ["sdr"],
            "encryption": ["plain"],
            "ladder": ["web", "tv", "full", "phone"],
            "package": ["hls"],
            "resolution": ["sd", "hd", "fhd"],
            "video_codec": ["h264", "h265"],
            "video_codec_non_secure": ["h264", "h265"],
        }
        drm = {
            "hdcp_version": ["HDCP_V2_2"],
            "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"],
        }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities="
        + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters="
        + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang="
        + parse.quote(lang)
    )


def extract_jhs_fallback_only(player_config):
    streams = []
    for key in ["media_asset", "media_asset_v2"]:
        assets = player_config.get(key)
        if not assets:
            continue
        if isinstance(assets, dict):
            assets = [assets]
        for asset in assets:
            for variant in ["fallback", "primary"]:
                item = asset.get(variant)
                if not isinstance(item, dict):
                    continue
                url = item.get("content_url")
                if url and (".m3u8" in url or ".mpd" in url):
                    streams.append(
                        {
                            "content_url": url,
                            "type": variant,
                            "playback_tags": item.get("playback_tags", ""),
                        }
                    )
    return streams


def extract_drm_info(player_config: dict):
    results = []
    seen = set()

    def find_license(obj, depth=0):
        if depth > 6 or not isinstance(obj, (dict, list)):
            return None
        if isinstance(obj, list):
            for item in obj:
                r = find_license(item, depth + 1)
                if r:
                    return r
        elif isinstance(obj, dict):
            for k in [
                "license_url",
                "licenseUrl",
                "widevine_license_url",
                "keyServerUrl",
                "key_server_url",
            ]:
                if k in obj and obj[k]:
                    return str(obj[k])
            for v in obj.values():
                r = find_license(v, depth + 1)
                if r:
                    return r
        return None

    license_url = find_license(player_config)
    for key in ["media_asset", "media_asset_v2"]:
        assets = player_config.get(key)
        if not assets:
            continue
        if isinstance(assets, dict):
            assets = [assets]
        for asset in assets:
            for variant in ["primary", "fallback"]:
                item = asset.get(variant)
                if not isinstance(item, dict):
                    continue
                url = item.get("content_url", "")
                if not url or ".mpd" not in url:
                    continue
                base = url.split("?")[0]
                if base in seen:
                    continue
                seen.add(base)
                item_license = (
                    item.get("license_url") or item.get("licenseUrl") or license_url
                )
                results.append(
                    {
                        "mpd_url": url,
                        "license_url": item_license,
                        "variant": variant.upper(),
                    }
                )
    return results


def fetch_drm_info_for_slug(slug_path: str):
    """c.py identical — DRM API → player_config → MPD list."""
    player_config = None
    try:
        api_url = build_drm_api_url(slug_path, "eng")
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=12) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                d = w.get("widget", {}).get("data", {})
                if "player_config" in d:
                    player_config = d["player_config"]
                    break
            if player_config:
                break
    except Exception:
        pass
    if not player_config:
        try:
            api_url2 = build_drm_api_url(slug_path, "hin")
            req2 = request.Request(api_url2, headers=build_headers())
            with request.urlopen(req2, timeout=12) as resp2:
                data2 = json.loads(resp2.read().decode("utf-8"))
            for sec in data2.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    d = w.get("widget", {}).get("data", {})
                    if "player_config" in d:
                        player_config = d["player_config"]
                        break
                if player_config:
                    break
        except Exception:
            pass
    if not player_config:
        return [], "", [], None
    drm_streams = extract_drm_info(player_config)
    return drm_streams, "", [], player_config


def get_hdntl_set_cookie_only(url: str, retries: int = 5) -> str:
    """Only Set-Cookie hdntl= (never fall back to query hdnea — that is 30m)."""
    if not url:
        return ""
    headers = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Referer": "https://www.hotstar.com/",
        "Origin": "https://www.hotstar.com",
        "Accept": "*/*",
    }
    for attempt in range(max(1, retries)):
        try:
            req = request.Request(url.split("|")[0].strip(), headers=headers)
            with request.urlopen(req, timeout=15) as resp:
                sc = resp.headers.get("Set-Cookie") or ""
                try:
                    all_sc = resp.headers.get_all("Set-Cookie") or []
                    if all_sc:
                        sc = "\n".join(all_sc)
                except Exception:
                    pass
                m = re.search(r"hdntl=([^;\s]+)", sc, flags=re.I)
                if m and "exp=" in m.group(1):
                    return m.group(1).strip()
        except Exception:
            pass
        if attempt + 1 < retries:
            time.sleep(0.4)
    return ""


def fetch_fresh_hdntl(input_url: str = None) -> str:
    """
    Exact c.py logic:
      DRM MPD → Set-Cookie hdntl
      else JHS live API streams → Set-Cookie hdntl
    Never uses query-string hdnea as the 24h cookie.
    """
    default = "https://www.hotstar.com/in/tv/star-sports-hindi-1/1260000025/live/watch"
    input_url = input_url or default
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        slug_path = _24H_DEFAULT_SLUG
    hdntl = ""

    # 1) DRM stream fetch (c.py)
    try:
        drm_streams, _, _, _ = fetch_drm_info_for_slug(slug_path)
        for stream in drm_streams:
            mpd_url = stream.get("mpd_url", "")
            if not mpd_url:
                continue
            hdntl = get_hdntl_set_cookie_only(mpd_url, retries=4)
            if hdntl:
                return hdntl
            # last resort: token already on MPD URL as hdntl= (rare)
            try:
                parsed = urlparse(mpd_url)
                params = parse_qs(parsed.query)
                if params.get("hdntl") and "exp=" in params["hdntl"][0]:
                    return params["hdntl"][0]
            except Exception:
                pass
    except Exception:
        pass

    # 2) JHS API fallback (c.py)
    try:
        jhs_api = build_jhs_api_url(slug_path, "hin", is_live=True)
        jhs_req = request.Request(jhs_api, headers=build_jhs_headers_android())
        with request.urlopen(jhs_req, timeout=12) as r:
            jhs_data = json.loads(r.read().decode("utf-8"))
        for sec in jhs_data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for ww in sec.get("widget_wrappers", []):
                pc = ww.get("widget", {}).get("data", {}).get("player_config")
                if not pc:
                    continue
                streams = extract_jhs_fallback_only(pc)
                for s in streams:
                    url = s.get("content_url", "")
                    if not url:
                        continue
                    hdntl = get_hdntl_set_cookie_only(url, retries=4)
                    if hdntl:
                        return hdntl
                    try:
                        parsed = urlparse(url)
                        params = parse_qs(parsed.query)
                        if params.get("hdntl") and "exp=" in params["hdntl"][0]:
                            return params["hdntl"][0]
                    except Exception:
                        pass
    except Exception:
        pass

    return hdntl or ""


# ===================== 24H COOKIE CACHE (c.py fetch_fresh_hdntl) =====================

def _hdntl_ttl_left(tok: str) -> int:
    if not tok:
        return 0
    m = re.search(r"exp=(\d+)", tok)
    if not m:
        return 0
    try:
        return max(0, int(m.group(1)) - int(time.time()))
    except Exception:
        return 0


def _strip_hdntl_prefix(tok: str) -> str:
    t = (tok or "").strip()
    if t.lower().startswith("hdntl="):
        t = t[6:]
    return t.strip()


def _with_hdntl_prefix(tok: str) -> str:
    t = _strip_hdntl_prefix(tok)
    return f"hdntl={t}" if t else ""


def get_24h_cookie_cached(force: bool = False) -> str:
    """
    c.py fetch_fresh_hdntl with token rotation. Cache 15h.
    Cookie is Set-Cookie hdntl (not query hdnea).

    **FIX**: If cached token has less than 5 hours remaining, force refresh.
    """
    global _24H_COOKIE_CACHE, _ACTIVE_TOKEN_OVERRIDE
    now = time.time()
    cached = _24H_COOKIE_CACHE.get("token") or ""
    age = now - float(_24H_COOKIE_CACHE.get("fetched_at") or 0)

    # NEW: Check if cached token is still valid for at least 5 hours
    ttl_ok = bool(cached and _hdntl_ttl_left(cached) > 5 * 3600)  # >5 hours
    if not force and cached and age < COOKIE_24H_TTL_SEC and ttl_ok:
        return cached

    # Try disk cache
    if not force and not cached:
        try:
            with open("hdntl_24h.cache", "r", encoding="utf-8") as _cf:
                disk = _strip_hdntl_prefix(_cf.read())
            if disk and _hdntl_ttl_left(disk) > 5 * 3600:
                _24H_COOKIE_CACHE["token"] = disk
                _24H_COOKIE_CACHE["fetched_at"] = time.time()
                return disk
        except Exception:
            pass

    tokens = []
    try:
        tokens = load_fhd_tokens()
    except Exception:
        tokens = []
    if not tokens:
        fb = load_user_token()
        if fb:
            tokens = [(0, fb, "token.txt")]
    if not tokens:
        print(f"  {YELLOW}⚠ No tokens for 24H cookie{RESET}")
        return cached

    start = int(_24H_COOKIE_CACHE.get("tok_idx") or 0) % len(tokens)
    for offset in range(min(len(tokens), 8)):
        idx = (start + offset) % len(tokens)
        num, tok_str, tpath = tokens[idx]
        label = os.path.basename(tpath) if tpath else f"token{num}"
        print(f"  {GRAY}→ 24H try {label} (c.py fetch_fresh_hdntl)...{RESET}", end="", flush=True)
        prev = _ACTIVE_TOKEN_OVERRIDE
        _ACTIVE_TOKEN_OVERRIDE = tok_str
        try:
            hdntl = fetch_fresh_hdntl(
                "https://www.hotstar.com/in/tv/star-sports-hindi-1/1260000025/live/watch"
            )
        finally:
            _ACTIVE_TOKEN_OVERRIDE = prev

        if hdntl and "exp=" in hdntl:
            hdntl = _strip_hdntl_prefix(hdntl)
            _24H_COOKIE_CACHE["token"] = hdntl
            _24H_COOKIE_CACHE["fetched_at"] = time.time()
            _24H_COOKIE_CACHE["tok_idx"] = (idx + 1) % len(tokens)
            left = _hdntl_ttl_left(hdntl)
            exp_m = re.search(r"exp=(\d+)", hdntl)
            exp_s = ""
            if exp_m:
                try:
                    exp_s = datetime.fromtimestamp(int(exp_m.group(1)), tz=IST).strftime(
                        "%Y-%m-%d %I:%M %p"
                    )
                except Exception:
                    exp_s = ""
            print(
                f" {GREEN}OK exp={exp_s or '?'} (~{left/3600:.1f}h) "
                f"hdntl (cache 15h){RESET}"
            )
            try:
                with open("hdntl_24h.cache", "w", encoding="utf-8") as _cf:
                    _cf.write(_with_hdntl_prefix(hdntl))
            except Exception:
                pass
            return hdntl
        print(f" {YELLOW}no Set-Cookie hdntl{RESET}")

    print(f"  {YELLOW}⚠ 24H hdntl not available{RESET}")
    return cached if _hdntl_ttl_left(cached) > 600 else ""


def append_hdntl_cookie_to_url(base_url: str, token: str) -> str:
    """
    24H c.py / JHS M3U format (hdntl only, no hdnea):
      https://host/.../index.mpd?|cookie=hdntl=TOKEN&referer=...&origin=...&user-agent=...
    """
    tok = _strip_hdntl_prefix(token)
    if not tok:
        return base_url
    raw = (base_url or "").split("|")[0].strip()
    # strip all query (auth lives in cookie= only)
    base = raw.split("?")[0]
    ua = M3U_USER_AGENT if "M3U_USER_AGENT" in globals() else "Hotstar;in.startv.hotstar/25.02.24.8.11169@rtxcric(Android/15)"
    from urllib.parse import quote as _q
    return (
        f"{base}?|"
        f"cookie=hdntl={tok}"
        f"&referer=https://www.hotstar.com/"
        f"&origin=https://www.hotstar.com"
        f"&user-agent={ua}"
    )


def build_24h_mpd_pipe(mpd_url: str, global_token: str, key_str: str = "") -> str:
    raw = (mpd_url or "").split("|")[0].strip()
    if not raw or not global_token:
        return raw
    return append_hdntl_cookie_to_url(raw, global_token)


def is_24h_stream_url(url: str) -> bool:
    return "ttl=86400" in (url or "").lower()


def is_24h_m3u_block(block: str) -> bool:
    if "24H" in (block or "") or "(24H)" in (block or ""):
        return True
    for line in (block or "").splitlines():
        if line.strip().startswith("http") and is_24h_stream_url(line):
            return True
    return False



def _available_langs_from_player_config(player_config: dict) -> list:
    """Detect audio languages advertised in player_config (playback_tags / deep keys)."""
    found = []
    seen = set()
    def _add(code_or_name: str):
        if not code_or_name:
            return
        s = str(code_or_name).strip()
        if not s:
            return
        low = s.lower()
        name = LANGUAGES.get(low) or LANGUAGES.get(low[:3]) or ""
        if not name:
            # already a display name?
            for _ln in UNIQUE_LANGUAGES.values():
                if _ln.lower() == low:
                    name = _ln
                    break
        if not name:
            name = s.upper()
        if name not in seen:
            seen.add(name)
            found.append(name)
    if not isinstance(player_config, dict):
        return found
    ptags = str(player_config.get("playback_tags") or "")
    for tag in ptags.split(";"):
        t = tag.strip()
        if t.lower().startswith("language:"):
            _add(t.split(":", 1)[1].strip())
    # common nested fields
    for key in ("languages", "audio_languages", "audioLanguages", "available_languages"):
        val = player_config.get(key)
        if isinstance(val, list):
            for item in val:
                if isinstance(item, str):
                    _add(item)
                elif isinstance(item, dict):
                    _add(item.get("iso3code") or item.get("code") or item.get("name") or item.get("language") or "")
        elif isinstance(val, str):
            for part in re.split(r"[,|;\s]+", val):
                _add(part)
    # shallow walk one level of nested dicts/lists for language-ish keys
    def _walk(obj, depth=0):
        if depth > 4 or obj is None:
            return
        if isinstance(obj, dict):
            for k, v in obj.items():
                kl = str(k).lower()
                if "lang" in kl and isinstance(v, (str, list)):
                    if isinstance(v, str):
                        _add(v)
                    else:
                        for it in v:
                            if isinstance(it, str):
                                _add(it)
                            elif isinstance(it, dict):
                                _add(it.get("iso3code") or it.get("code") or it.get("name") or "")
                else:
                    _walk(v, depth + 1)
        elif isinstance(obj, list) and depth < 3:
            for it in obj[:30]:
                _walk(it, depth + 1)
    _walk(player_config, 0)
    return found



# ===================== ADS-FREE 4K HEAVY (hot.py option 7 style) =====================
API_TEMPLATE_4KADS = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug_path}/watch"

LANG_MAP_4KADS = {
    "1": ["eng", "en"],
    "2": ["hin", "hi", "hd"],
    "3": ["mar", "mr", "ma"],
    "4": ["guj", "gu"],
    "5": ["bho", "bh", "bih"],
    "6": ["pan", "pun", "pa", "pu"],
    "7": ["har", "hv", "ha"],
    "8": ["tam", "ta"],
    "9": ["tel", "te"],
    "10": ["kan", "kn"],
    "11": ["mal", "ml"],
    "12": ["ben", "bn"],
}
LANG_DISPLAY_4KADS = {
    "eng": "ENGLISH", "en": "ENGLISH",
    "hin": "HINDI", "hi": "HINDI", "hd": "HINDI",
    "mar": "MARATHI", "mr": "MARATHI", "ma": "MARATHI",
    "guj": "GUJARATI", "gu": "GUJARATI",
    "bho": "BHOJPURI", "bh": "BHOJPURI", "bih": "BHOJPURI",
    "pan": "PUNJABI", "pun": "PUNJABI", "pa": "PUNJABI", "pu": "PUNJABI",
    "har": "HARYANVI", "hv": "HARYANVI", "ha": "HARYANVI",
    "tam": "TAMIL", "ta": "TAMIL",
    "tel": "TELUGU", "te": "TELUGU",
    "kan": "KANNADA", "kn": "KANNADA",
    "mal": "MALAYALAM", "ml": "MALAYALAM",
    "ben": "BENGALI", "bn": "BENGALI",
}
LANG_ORDER_4KADS = [
    "ENGLISH", "HINDI", "MARATHI", "GUJARATI", "BHOJPURI", "PUNJABI",
    "HARYANVI", "TAMIL", "TELUGU", "KANNADA", "MALAYALAM", "BENGALI",
]

_4K_TOKEN_CACHE = {
    "tokens": [],       # all loaded (num, tok, path)
    "valid": [],        # validated only
    "loaded_at": 0.0,
    "checked_at": 0.0,
    "rot_idx": 0,
    "rot_slot": -1,     # minute slot used for last pick
}
_4K_TOKEN_VALID_CACHE_FILE = os.path.join(_SCRIPT_DIR, ".fhd_4k_token_valid_cache.json")
_4K_TOKEN_ROTATE_SEC = 60  # rotate 4K user-token every 60s (same idea as FHD)


def load_4k_tokens() -> list:
    """Load token*.txt from TOKEN_4K_DIR (separate pool for 4K streams)."""
    global _4K_TOKEN_CACHE
    tok_dir = TOKEN_4K_DIR
    found = []
    try:
        if os.path.isdir(tok_dir):
            for name in sorted(os.listdir(tok_dir)):
                if not (name.startswith("token") and name.endswith(".txt")):
                    continue
                fpath = os.path.join(tok_dir, name)
                try:
                    with open(fpath, "r", encoding="utf-8") as f:
                        tok = f.read().strip()
                    if tok:
                        num = re.sub(r"\D", "", name) or "0"
                        found.append((int(num) if num.isdigit() else 0, tok, fpath))
                except Exception:
                    pass
    except Exception:
        pass
    _4K_TOKEN_CACHE["tokens"] = found
    _4K_TOKEN_CACHE["loaded_at"] = time.time()
    return found


def validate_4k_tokens(all_tokens: list = None) -> list:
    """p.py-style parallel validate for 4K token pool."""
    global _4K_TOKEN_CACHE
    if all_tokens is None:
        all_tokens = _4K_TOKEN_CACHE.get("tokens") or load_4k_tokens()
    n = len(all_tokens)
    if not n:
        _4K_TOKEN_CACHE["valid"] = []
        return []

    t0 = time.time()
    cache = {}
    try:
        if os.path.isfile(_4K_TOKEN_VALID_CACHE_FILE):
            with open(_4K_TOKEN_VALID_CACHE_FILE, "r", encoding="utf-8") as f:
                blob = json.load(f)
            if time.time() - float(blob.get("ts") or 0) < 1800:
                cache = blob.get("map") or {}
    except Exception:
        cache = {}

    results = {}
    need_check = []
    for tn, ts, p in all_tokens:
        fp = (ts or "")[:64]
        if fp in cache and cache[fp] in ("ok", "bad"):
            results[tn] = cache[fp]
        else:
            need_check.append((tn, ts))

    if need_check:
        print(f"{CYAN}Checking {len(need_check)}/{n} 4K tokens in parallel (cache hit {n - len(need_check)})...{RESET}")
    else:
        print(f"{CYAN}4K token cache hit — all {n} tokens...{RESET}")

    def _chk(tok_num, tok_str):
        return tok_num, tok_str, check_token_valid_fast(tok_str)

    if need_check:
        with ThreadPoolExecutor(max_workers=min(max(len(need_check), 1), 40)) as pool:
            futs = {pool.submit(_chk, tn, ts): tn for tn, ts in need_check}
            for f in as_completed(futs):
                try:
                    tn, ts, status = f.result()
                    results[tn] = status
                    if status in ("ok", "bad"):
                        cache[(ts or "")[:64]] = status
                except Exception:
                    results[futs[f]] = "unknown"
        try:
            with open(_4K_TOKEN_VALID_CACHE_FILE, "w", encoding="utf-8") as f:
                json.dump({"ts": time.time(), "map": cache}, f)
        except Exception:
            pass

    elapsed = time.time() - t0
    valid = [t for t in all_tokens if results.get(t[0], "unknown") in ("ok", "unknown")]
    invalid = [t for t in all_tokens if results.get(t[0]) == "bad"]
    n_ok = sum(1 for t in all_tokens if results.get(t[0]) == "ok")
    n_unk = sum(1 for t in all_tokens if results.get(t[0]) == "unknown")
    usable = len(valid)
    print(f"{GREEN}✓ 4K Valid: {usable}/{n} tokens  ({elapsed:.1f}s){RESET}"
          + (f"  {GRAY}(ok={n_ok}, timeout={n_unk}){RESET}" if n_unk else ""))
    if invalid:
        names = [f"token{t[0]}.txt" if t[0] else "token.txt" for t in invalid]
        print(f"{RED}  4K Expired: {', '.join(names[:20])}{'...' if len(names) > 20 else ''}{RESET}")
    _4K_TOKEN_CACHE["valid"] = valid
    _4K_TOKEN_CACHE["tokens"] = all_tokens
    _4K_TOKEN_CACHE["checked_at"] = time.time()
    return valid



def _pick_4k_token() -> str:
    """Time-based rotation across validated 4K tokens (60s slot)."""
    toks = _4K_TOKEN_CACHE.get("valid") or _4K_TOKEN_CACHE.get("tokens") or load_4k_tokens()
    if not toks:
        return load_user_token() or ""
    slot = int(time.time() // _4K_TOKEN_ROTATE_SEC)
    if _4K_TOKEN_CACHE.get("rot_slot") != slot:
        _4K_TOKEN_CACHE["rot_slot"] = slot
        _4K_TOKEN_CACHE["rot_idx"] = slot % len(toks)
    idx = int(_4K_TOKEN_CACHE.get("rot_idx") or 0) % len(toks)
    return toks[idx][1]


def build_headers_4kads(token: str = "") -> dict:
    """Exact hot.py build_headers_4kads."""
    ua, cs, app_code = _get_atv_device()
    h = HEADERS_BASE_4KADS.copy()
    h["User-Agent"] = ua
    h["X-HS-Client"] = cs
    h["X-HS-Platform"] = "androidtv"
    h["x-hs-app"] = app_code
    tok = (token or "").strip() or _pick_4k_token() or load_user_token() or ""
    h["x-hs-usertoken"] = tok
    h["X-Request-Id"] = str(uuid.uuid4())
    h["x-hs-request-id"] = str(uuid.uuid4())
    h["x-hs-device-id"] = str(uuid.uuid4())
    h["Accept"] = "application/json, text/plain, */*"
    h["Referer"] = "https://www.hotstar.com/in/"
    h["Origin"] = "https://www.hotstar.com"
    h["X-Country-Code"] = "in"
    h["X-HS-Accept-language"] = "eng"
    return h


def build_api_url_4kads(slug_path: str, lang: str, sdr_only: bool = False) -> str:
    """
    SDR → option 5 JHS 4K (working *4kssai packages)
    HDR → option 7 ADS-FREE 4K HEAVY (hdr10)
    """
    base_url = API_TEMPLATE_4KADS.format(slug_path=slug_path)
    if sdr_only:
        # option 5 JHS 4K — was working for all SDR
        client_capabilities = {
            "ads": ["ssai"],
            "audio_channel": ["stereo", "dolby51", "atmos"],
            "container": ["ts", "fmp4"],
            "dvr": ["short"],
            "dynamic_range": ["sdr"],
            "encryption": ["plain"],
            "ladder": ["tv", "full"],
            "package": ["hls", "dash"],
            "resolution": ["hd", "fhd", "4k"],
            "true_resolution": ["hd", "4k"],
            "video_codec": ["h265", "h264"],
        }
        drm_parameters = {"widevine_security_level": ["SW_SECURE_DECODE"]}
    else:
        # option 7 ADS-FREE 4K HEAVY — real HDR
        client_capabilities = {
            "ads": ["non_ssai", "ssai"],
            "audio_channel": ["stereo", "dolby51", "atmos"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short", "long"],
            "dynamic_range": ["hdr10", "hdr", "sdr"],
            "encryption": ["widevine", "plain"],
            "ladder": ["tv", "web", "phone", "4k"],
            "package": ["dash", "hls"],
            "resolution": ["4k", "fhd", "hd", "sd"],
            "video_codec": ["h265", "h264"],
            "video_codec_non_secure": ["h265", "h264", "vp9"],
        }
        drm_parameters = {
            "hdcp_version": ["HDCP_V2_2"],
            "widevine_security_level": [
                "HW_SECURE_ALL", "HW_SECURE_DECODE", "SW_SECURE_DECODE"
            ],
        }
    return (
        base_url
        + "?search_query=live"
        + "&client_capabilities="
        + parse.quote(json.dumps(client_capabilities, separators=(",", ":")))
        + "&drm_parameters="
        + parse.quote(json.dumps(drm_parameters, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang="
        + parse.quote(lang, safe="")
    )


def _4k_token_list() -> list:
    out, seen = [], set()
    for item in (_4K_TOKEN_CACHE.get("tokens") or load_4k_tokens() or []):
        tok = item[1] if isinstance(item, (list, tuple)) and len(item) > 1 else ""
        if tok and tok not in seen:
            seen.add(tok)
            out.append(tok)
    try:
        fb = load_user_token()
        if fb and fb not in seen:
            out.append(fb)
    except Exception:
        pass
    return out


def _event_eligible_for_4k(ev_title: str, ev_url: str) -> bool:
    t = (ev_title or "").lower()
    u = (ev_url or "").lower()
    if "live show" in t or "/shows/" in u:
        return False
    if re.search(r"\bbbs?\d*\b", t) or "24x7" in t or "24 hrs" in t or "[deferred]" in t:
        return False
    if "bigg boss" in t or "biggboss" in u:
        return False
    return True



def _is_bad_cf_token_url(url: str) -> bool:
    """CloudFront residue / bad cookie style that does not play on liveNNp."""
    u = (url or "")
    low = u.lower()
    if "signature=" in low or "key-pair-id=" in low or "expires=" in low:
        return True
    # standalone CF ttl on query (not inside hdnea)
    if re.search(r"(?:^|[?&])ttl=86400(?:&|$)", u):
        return True
    return False


def _token_is_good_path_acl(url: str) -> bool:
    """Working option5 tokens: path ACL (acl=%2f... or acl=/out or acl=/cmaf) + exp."""
    try:
        tok = extract_hdntl_from_url(url) or ""
        tok = _strip_hdntl_prefix(tok) if tok else ""
    except Exception:
        tok = ""
    if not tok or "exp=" not in tok:
        return False
    low = tok.lower()
    # encoded path ACL is best (working hindi4kssai style)
    if "acl=%2f" in low or "acl=%2fout" in low or "acl=%2fcmaf" in low:
        return True
    if "acl=/out" in low or "acl=/cmaf" in low or "acl=/hls" in low:
        return True
    return False


def rewrite_url_to_clean_cdn_4k(url: str) -> str:
    """
    JHS 4K (option 5) style CDN rewrite:
      *4kssai / /out/v1/ packages:
        live11mp-ssai-akt-... → live11mp.hotstar.com
        live12mp-ssai-akt-... → live12mp.hotstar.com
      cmaf regional:
        live14p-ssai-akt-... → live14p.hotstar.com
    """
    try:
        parsed = urlparse(url)
        raw_query = parsed.query or ""
        path_l = (parsed.path or "").lower()
        host = (parsed.netloc or "").lower()
        is_4kssai = ("4kssai" in path_l) or ("4khdr" in path_l) or (
            "/out/v1/" in path_l and "4k" in path_l
        )

        # Detect liveNNmp or liveNNp from host or playback_host
        live_mp = ""
        live_p = ""
        ph_match = re.search(r"(?:^|&)playback_host=([^&]+)", raw_query)
        sources = [host]
        if ph_match:
            sources.append(unquote(ph_match.group(1)).lower())
        for src in sources:
            m_mp = re.match(r"(live\d+mp)(?:-|\.|$)", src, re.I)
            if m_mp and not live_mp:
                live_mp = m_mp.group(1).lower()
            m_p = re.match(r"(live\d+p)(?:-|\.|$)", src, re.I)
            if m_p and not live_p and "mp" not in m_p.group(1).lower():
                live_p = m_p.group(1).lower()

        if is_4kssai and live_mp:
            clean_host = f"{live_mp}.hotstar.com"
        elif is_4kssai and re.match(r"live\d+mp", host):
            m = re.match(r"(live\d+mp)", host)
            clean_host = f"{m.group(1)}.hotstar.com"
        elif live_p:
            clean_host = f"{live_p}.hotstar.com"
        elif re.match(r"live\d+p-ssai", host) and "mp" not in host:
            m = re.match(r"(live\d+p)", host)
            clean_host = f"{m.group(1)}.hotstar.com" if m else ""
        else:
            return url

        if not clean_host:
            return url
        cf_strip = {"signature", "expires", "key-pair-id"}
        kept = []
        for part in raw_query.split("&"):
            if not part:
                continue
            key = part.split("=", 1)[0].strip().lower()
            if key in cf_strip:
                continue
            kept.append(part)
        return urlunparse(parsed._replace(netloc=clean_host, query="&".join(kept)))
    except Exception:
        return url


def is_cloudfront_url_4k(url: str) -> bool:
    try:
        host = urlparse(url).netloc.lower()
        if "Signature=" in url or "Key-Pair-Id=" in url:
            return True
        if "live-ssai-cf" in host or "cloudfront.net" in host:
            return True
        if host == "live-cf.cdn.hotstar.com" or host.endswith(".live-cf.cdn.hotstar.com"):
            return True
    except Exception:
        pass
    return False


def is_blacklisted_cdn_4k(host: str) -> bool:
    host = (host or "").lower()
    if host.endswith(".live-cf.cdn.hotstar.com") or host == "live-cf.cdn.hotstar.com":
        return True
    return False


def detect_language_from_url_4kads(url: str) -> str:
    """Exact hot.py-style language detect from URL."""
    return _lang_from_stream_url(url, "") or "OTHER"


def fetch_player_config_4kads(api_url: str, token: str = "") -> dict:
    req = request.Request(api_url, headers=build_headers_4kads(token))
    with request.urlopen(req, timeout=18) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    try:
        pc = data["success"]["page"]["spaces"]["player"]["widget_wrappers"][0]["widget"]["data"]["player_config"]
        if pc:
            return pc
    except Exception:
        pass
    page_spaces = (data.get("success") or {}).get("page", {}).get("spaces", {}) or {}
    for sec in page_spaces.values():
        for w in sec.get("widget_wrappers", []) or []:
            d = (w.get("widget") or {}).get("data") or {}
            if d.get("player_config"):
                return d["player_config"]
    raise ValueError("Could not find player_config")


def extract_all_streams_4kads(player_config: dict) -> list:
    streams = []
    media_assets = []
    for key in ("media_asset", "media_asset_v2", "media_assets"):
        asset = (player_config or {}).get(key)
        if not asset:
            continue
        if isinstance(asset, dict):
            media_assets.append(asset)
        elif isinstance(asset, list):
            media_assets.extend(asset)
    for asset in media_assets:
        if not isinstance(asset, dict):
            continue
        for stream_type in ("primary", "fallback", "preview", "dash", "hls", "playback_url"):
            item = asset.get(stream_type)
            if not isinstance(item, dict):
                continue
            content_url = (
                item.get("content_url")
                or item.get("url")
                or item.get("playback_url")
            )
            if not content_url:
                continue
            streams.append({
                "type": stream_type,
                "content_url": content_url,
                "playback_tags": str(item.get("playback_tags", "") or "").lower(),
                "width": item.get("width") or 0,
                "height": item.get("height") or 0,
            })
    unique, seen = [], set()
    for s in streams:
        url = s.get("content_url") or ""
        clean = url.split("?")[0]
        if not clean or clean in seen:
            continue
        seen.add(clean)
        unique.append(s)
    return unique


def get_hdntl_token_4kads(url: str, retries: int = 5) -> str:
    """Exact hot.py get_hdntl_token_4kads — Set-Cookie then URL fallback."""
    target = (url or "").split("|")[0].strip()
    if not target:
        return ""
    headers = {
        "User-Agent": HEADERS_BASE_4KADS.get(
            "User-Agent",
            "Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)",
        ),
        "Referer": "https://www.hotstar.com/",
        "Origin": "https://www.hotstar.com",
        "Accept": "*/*",
    }
    for attempt in range(max(1, retries)):
        try:
            req = request.Request(target, headers=headers)
            with request.urlopen(req, timeout=15) as resp:
                set_cookie = resp.headers.get("Set-Cookie", "") or ""
                try:
                    all_sc = resp.headers.get_all("Set-Cookie") or []
                    if all_sc:
                        set_cookie = "\n".join(all_sc)
                except Exception:
                    pass
                if "hdntl=" in set_cookie:
                    m = re.search(r"hdntl=([^;\s,]+)", set_cookie, flags=re.I)
                    if m and "exp=" in m.group(1):
                        return m.group(1).strip()
        except Exception:
            pass
        time.sleep(0.5)
    # Fallback to query token (API path-ACL)
    try:
        params = parse_qs(urlparse(target).query)
        for key in ("hdnea", "hdntl"):
            if key in params and params[key] and "exp=" in (params[key][0] or ""):
                return params[key][0]
    except Exception:
        pass
    return ""


def append_hdntl_to_url_4kads(base_url: str, token: str) -> str:
    """Exact hot.py append_hdntl_to_url_4kads."""
    if not token:
        return base_url
    if "?" in base_url:
        base_part, query_part = base_url.split("?", 1)
        params = query_part.split("&")
        new_params = [
            p for p in params
            if not (
                p.startswith("hdnea=")
                or p.startswith("hdntl=")
                or p.startswith("ttl=")
                or p.startswith("Expires=")
                or p.startswith("Signature=")
                or p.startswith("Key-Pair-Id=")
            )
        ]
        base_url = base_part + (("?" + "&".join(new_params)) if new_params else "")
    if "?" in base_url:
        return base_url + "&hdnea=" + token
    return base_url + "?hdnea=" + token


def _embed_hdntl_in_url(url: str) -> str:
    """
    Keep API-issued hdnea always when present (option7 working TXT style).
    Only Set-Cookie when URL has no token at all.
    """
    raw = (url or "").split("|")[0].strip()
    if not raw:
        return url
    existing = ""
    try:
        existing = extract_hdntl_from_url(raw) or ""
        if existing:
            existing = _strip_hdntl_prefix(existing)
    except Exception:
        existing = ""
    if existing and "exp=" in existing:
        return raw  # ALWAYS keep API token
    token = get_hdntl_token_4kads(raw, retries=6)
    if token:
        try:
            token = _strip_hdntl_prefix(token)
        except Exception:
            pass
        return append_hdntl_to_url_4kads(raw, token)
    return raw




def _fix_mp_ssai_to_jiol(url: str) -> str:
    """*4kssai / out/v1: liveNNmp-ssai-akt-... → liveNNmp.hotstar.com (JHS 4K option5)."""
    try:
        return rewrite_url_to_clean_cdn_4k(url)
    except Exception:
        return url


def fetch_stream_4kads_lite(
    slug_path: str,
    lang_codes: list,
    expected_lang: str,
    use_sdr: bool = False,
    max_retries: int = 16,
    prefer_out_v1_4k: bool = False,
) -> str:
    """
    True 4K only (height>=2160 or 4kssai/4khdr markers).
    Rejects FHD packaged as fake 4K.
    """
    tokens = _4k_token_list() or [""]
    start_i = int(time.time()) % max(1, len(tokens))
    ordered_toks = tokens[start_i:] + tokens[:start_i]

    def _is_true_4k(url: str, tags: str, height: int) -> bool:
        ul = (url or "").lower()
        t = (tags or "").lower()
        if height >= 2160:
            return True
        if "4kssai" in ul or "4khdr" in ul or "english4k" in ul or "hindi4k" in ul:
            return True
        if "/out/v1/" in ul and "4k" in ul:
            return True
        if re.search(r"(?:^|[;,\s])(?:resolution|video_quality):(?:4k|uhd)(?:$|[;,\s])", t):
            return True
        if "4k" in t and "fhd" not in t and height >= 2160:
            return True
        # reject common FHD-only paths
        if height and height < 2160:
            return False
        if "fhd" in ul and "4k" not in ul:
            return False
        return False

    for attempt in range(max_retries):
        tok = ordered_toks[attempt % len(ordered_toks)]
        for lang_code in lang_codes:
            try:
                if attempt > 0:
                    time.sleep(0.25)
                api_url = build_api_url_4kads(slug_path, lang_code, sdr_only=use_sdr)
                player_config = fetch_player_config_4kads(api_url, tok)
                if not player_config:
                    continue

                best = ""
                best_score = -999
                for key in ("media_asset", "media_asset_v2"):
                    assets = player_config.get(key)
                    if not assets:
                        continue
                    if isinstance(assets, dict):
                        assets = [assets]
                    for asset in assets:
                        if not isinstance(asset, dict):
                            continue
                        # ONLY primary (no fallback CDN packages)
                        for variant in ("primary",):
                            item = asset.get(variant)
                            if not isinstance(item, dict):
                                continue
                            url = item.get("content_url") or ""
                            if not url or ".m3u8" not in url:
                                continue
                            if is_cloudfront_url_4k(url) or _is_bad_cf_token_url(url):
                                continue
                            tags = str(item.get("playback_tags", "") or "").lower()
                            try:
                                height = int(item.get("height") or 0)
                            except Exception:
                                height = 0
                            vq = str(item.get("video_quality", "") or "").lower()
                            res = str(item.get("resolution", "") or "").lower()
                            tags_all = tags + f";{vq};{res}"
                            if not _is_true_4k(url, tags_all, height):
                                continue
                            ul = url.lower()
                            detected = detect_language_from_url_4kads(url)
                            if detected and detected != "OTHER" and detected.upper() != expected_lang.upper():
                                continue
                            # Prefer playback_host links (clean CDN rewrite source)
                            has_ph = "playback_host=" in ul
                            score = 20  # primary only
                            if has_ph:
                                score += 40
                            if height >= 2160:
                                score += 30
                            if use_sdr:
                                if "4kssai" in ul:
                                    score += 50
                                if "/out/v1/" in ul:
                                    score += 30
                                if "4khdr" in ul:
                                    score -= 40
                            else:
                                if "4khdr" in ul or "hdr10" in ul:
                                    score += 50
                                if "hdr" in tags_all:
                                    score += 25
                                if "4kssai" in ul and "hdr" not in ul:
                                    score -= 20
                            if _token_is_good_path_acl(url):
                                score += 15
                            if score > best_score:
                                best_score = score
                                best = url

                if best:
                    final = rewrite_url_to_clean_cdn_4k(best)
                    if is_cloudfront_url_4k(final) or _is_bad_cf_token_url(final):
                        continue
                    # Prefer rewritten host from playback_host (liveNNmp / liveNNp.hotstar.com)
                    if "playback_host=" not in final.lower() and "playback_host=" in best.lower():
                        # keep playback_host query after rewrite
                        try:
                            from urllib.parse import parse_qs, urlencode
                            bq = parse_qs(urlparse(best).query)
                            fq = parse_qs(urlparse(final).query)
                            if "playback_host" in bq and "playback_host" not in fq:
                                fq["playback_host"] = bq["playback_host"]
                                p = urlparse(final)
                                # flatten single values
                                flat = {k: (v[0] if isinstance(v, list) and len(v)==1 else v) for k, v in fq.items()}
                                final = urlunparse(p._replace(query=urlencode(flat, doseq=True)))
                        except Exception:
                            pass
                    return final
            except Exception:
                continue
    return ""




def fetch_stream_4k_mpd(
    slug_path: str,
    lang_codes: list,
    expected_lang: str,
    use_sdr: bool = False,
    max_retries: int = 10,
) -> tuple:
    """
    hot.py option {1} NORMAL 4K style — DASH/MPD only.
    Returns (mpd_url, player_config, is_hdr) or ("", {}, False).
    Never returns .m3u8.
    """
    tokens = _4k_token_list() or [""]
    start_i = int(time.time()) % max(1, len(tokens))
    ordered_toks = tokens[start_i:] + tokens[:start_i]

    def _is_4k_candidate(url: str, item: dict, tags: str) -> bool:
        """Same rules as hot.py extract_4k_streams + must be .mpd."""
        ul = (url or "").lower()
        if ".mpd" not in ul:
            return False
        if ".m3u8" in ul:
            return False
        try:
            height = int(item.get("height") or 0)
        except Exception:
            height = 0
        vq = str(item.get("video_quality", "") or "").lower()
        res = str(item.get("resolution", "") or "").lower()
        t = (tags or "").lower()
        # NORMAL 4K packages often live under /mp1/ /mp2/ paths
        path_4k = any(x in ul for x in ("/mp1/", "/mp2/", "/mp3/", "_4k", "/4k/", "4k"))
        return (
            "4k" in t or height >= 2160 or "4k" in vq or "4k" in res
            or path_4k or "uhd" in t or "uhd" in ul
        )

    for attempt in range(max_retries):
        tok = ordered_toks[attempt % len(ordered_toks)]
        for lang_code in lang_codes:
            try:
                if attempt > 0:
                    time.sleep(0.15)
                # Prefer NORMAL 4K capabilities (hot.py quality_choice == "1")
                try:
                    api_url = build_api_url(slug_path, lang_code, "1")
                except Exception:
                    api_url = build_api_url_4kads(slug_path, lang_code, sdr_only=use_sdr)
                player_config = fetch_player_config_4kads(api_url, tok)
                if not player_config:
                    try:
                        api2 = build_drm_api_url(slug_path, lang_code)
                        player_config = fetch_player_config_4kads(api2, tok)
                    except Exception:
                        player_config = None
                if not player_config:
                    continue

                best = ""
                best_score = -999
                best_hdr = False
                for key in ("media_asset", "media_asset_v2"):
                    assets = player_config.get(key)
                    if not assets:
                        continue
                    if isinstance(assets, dict):
                        assets = [assets]
                    for asset in assets:
                        if not isinstance(asset, dict):
                            continue
                        for variant in ("primary", "fallback"):
                            item = asset.get(variant)
                            if not isinstance(item, dict):
                                continue
                            url = item.get("content_url") or item.get("url") or ""
                            if not url:
                                continue
                            ul0 = url.lower()
                            # HARD: only .mpd — never m3u8 in MPD slot
                            if ".mpd" not in ul0 or ".m3u8" in ul0:
                                continue
                            if is_cloudfront_url_4k(url) or _is_bad_cf_token_url(url):
                                continue
                            tags = str(item.get("playback_tags", "") or "").lower()
                            if not _is_4k_candidate(url, item, tags):
                                continue
                            detected = detect_language_from_url_4kads(url)
                            if detected and detected != "OTHER" and detected.upper() != expected_lang.upper():
                                # soft: still allow if path has no lang segment
                                if detected.upper() in ("ENGLISH", "HINDI") and expected_lang.upper() in ("ENGLISH", "HINDI"):
                                    if detected.upper() != expected_lang.upper():
                                        continue
                            try:
                                height = int(item.get("height") or 0)
                            except Exception:
                                height = 0
                            ul = ul0
                            tags_all = tags + ";" + str(item.get("video_quality", "")).lower()
                            score = 30 if variant == "primary" else 10
                            if height >= 2160:
                                score += 40
                            if "/mp1/" in ul or "/mp2/" in ul or "/mp3/" in ul:
                                score += 25  # NORMAL 4K DASH package path
                            is_hdr = (
                                "hdr" in tags_all or "hdr10" in ul or "4khdr" in ul
                                or str(player_config.get("dynamic_range", "")).lower() in ("hdr", "hdr10")
                            )
                            if use_sdr and is_hdr:
                                score -= 35
                            if not use_sdr and is_hdr:
                                score += 35
                            if score > best_score:
                                best_score = score
                                best = url
                                best_hdr = is_hdr

                if best and ".mpd" in best.lower() and ".m3u8" not in best.lower():
                    final = best
                    try:
                        final = rewrite_url_to_clean_cdn_4k(best)
                    except Exception:
                        final = best
                    # rewrite must not turn MPD into HLS
                    if ".mpd" not in (final or "").lower() or ".m3u8" in (final or "").lower():
                        final = best
                    if is_cloudfront_url_4k(final) or _is_bad_cf_token_url(final):
                        continue
                    if ".mpd" not in final.lower():
                        continue
                    return final, player_config, best_hdr
            except Exception:
                continue
    return "", {}, False



def fetch_event_4k_entries(ev_title: str, ev_url: str) -> list:
    """
    hot.py option 5 — JHS 4K.
    *4kssai packages → liveNNmp.hotstar.com; regionals → liveNNp.hotstar.com.
    """
    if not _event_eligible_for_4k(ev_title, ev_url):
        return []
    slug = extract_slug_path(ev_url)
    if not slug:
        return []
    if not _4K_TOKEN_CACHE.get("tokens"):
        load_4k_tokens()

    # Step 1: option 7 HDR — ENGLISH + HINDI (fast, few retries)
    hdr_results = {}
    eng_hdr = fetch_stream_4kads_lite(
        slug, LANG_MAP_4KADS.get("1", ["eng"]), "ENGLISH", use_sdr=False, max_retries=16
    )
    if eng_hdr:
        hdr_results["ENGLISH HDR"] = eng_hdr
    hin_hdr = fetch_stream_4kads_lite(
        slug, LANG_MAP_4KADS.get("2", ["hin", "hi", "hd"]), "HINDI", use_sdr=False, max_retries=16
    )
    if hin_hdr:
        hdr_results["HINDI HDR"] = hin_hdr

    # Step 2: option 5 JHS SDR — all langs in parallel (fast)
    sdr_results = {}
    def _one_sdr(lang_codes):
        expected = LANG_DISPLAY_4KADS.get(lang_codes[0], "ENGLISH")
        prefer = expected in ("ENGLISH", "HINDI")
        url = fetch_stream_4kads_lite(
            slug, lang_codes, expected, use_sdr=True, max_retries=16,
            prefer_out_v1_4k=prefer,
        )
        return expected, url or ""

    with ThreadPoolExecutor(max_workers=min(8, len(LANG_MAP_4KADS))) as ex:
        futs = [ex.submit(_one_sdr, codes) for _, codes in LANG_MAP_4KADS.items()]
        for fut in as_completed(futs):
            try:
                expected, url = fut.result()
            except Exception:
                continue
            if not url:
                continue
            if expected in ("ENGLISH", "HINDI"):
                sdr_results[f"{expected} SDR"] = url
            else:
                sdr_results[expected] = url

    all_raw = {}
    all_raw.update(hdr_results)
    all_raw.update(sdr_results)
    if not all_raw:
        print(f"  {GRAY}· 4K not available: {(ev_title or '')[:50]}{RESET}")
        return []

    # Step 3: embed hdntl (option7)
    embedded = {}
    with ThreadPoolExecutor(max_workers=min(8, len(all_raw))) as ex:
        futs = {ex.submit(_embed_hdntl_in_url, u): lab for lab, u in all_raw.items()}
        for fut in as_completed(futs):
            lab = futs[fut]
            try:
                embedded[lab] = fut.result() or all_raw[lab]
            except Exception:
                embedded[lab] = all_raw[lab]

    # Step 4: entries — ENG/HIN HDR+SDR only once each; regionals once
    entries = []
    seen_path = set()
    for lab in ("ENGLISH HDR", "HINDI HDR"):
        if lab not in embedded:
            continue
        url = embedded[lab]
        pk = url.split("?")[0].lower()
        if pk in seen_path:
            continue
        seen_path.add(pk)
        entries.append((f"{lab} 4K", url, True, {}, url))
    for lab in ("ENGLISH SDR", "HINDI SDR"):
        if lab not in embedded:
            continue
        url = embedded[lab]
        pk = url.split("?")[0].lower()
        if pk in seen_path:
            continue
        seen_path.add(pk)
        entries.append((f"{lab} 4K", url, False, {}, url))
    for name in LANG_ORDER_4KADS:
        if name in ("ENGLISH", "HINDI"):
            continue
        if name not in embedded:
            continue
        url = embedded[name]
        pk = url.split("?")[0].lower()
        if pk in seen_path:
            continue
        seen_path.add(pk)
        entries.append((f"{name} 4K", url, False, {}, url))

    # ---- 4K MPD (DASH): same format as FHD MPD → (30M) + (24H) ----
    # ENG/HIN HDR+SDR + regionals when API returns true-4K .mpd
    mpd_jobs = []
    # HDR first
    mpd_jobs.append(("ENGLISH", LANG_MAP_4KADS.get("1", ["eng"]), False))
    mpd_jobs.append(("HINDI", LANG_MAP_4KADS.get("2", ["hin", "hi"]), False))
    # SDR
    mpd_jobs.append(("ENGLISH", LANG_MAP_4KADS.get("1", ["eng"]), True))
    mpd_jobs.append(("HINDI", LANG_MAP_4KADS.get("2", ["hin", "hi"]), True))
    for name in LANG_ORDER_4KADS:
        if name in ("ENGLISH", "HINDI"):
            continue
        codes = None
        for _k, v in LANG_MAP_4KADS.items():
            if LANG_DISPLAY_4KADS.get(v[0], "").upper() == name:
                codes = v
                break
        if codes:
            mpd_jobs.append((name, codes, True))

    def _one_mpd(job):
        expected, codes, use_sdr = job
        url, pc, is_hdr = fetch_stream_4k_mpd(
            slug, codes, expected, use_sdr=use_sdr, max_retries=8
        )
        return expected, url, pc, is_hdr, use_sdr

    mpd_results = []
    with ThreadPoolExecutor(max_workers=min(6, max(2, len(mpd_jobs)))) as ex:
        futs = [ex.submit(_one_mpd, j) for j in mpd_jobs]
        for fut in as_completed(futs):
            try:
                mpd_results.append(fut.result())
            except Exception:
                continue

    def _probe_mpd_reachable(u: str) -> bool:
        """Quick GET — must return MPD XML (working CDN)."""
        try:
            raw = (u or "").split("|")[0].strip()
            if not raw:
                return False
            tok = extract_hdntl_from_url(raw) or ""
            headers = {
                "User-Agent": M3U_USER_AGENT,
                "Referer": M3U_REFERER,
                "Origin": M3U_ORIGIN,
            }
            if tok:
                headers["Cookie"] = f"hdntl={_strip_hdntl_prefix(tok)}"
            req = request.Request(raw, headers=headers)
            with request.urlopen(req, timeout=10) as resp:
                chunk = resp.read(4096)
            low = chunk[:200].lower()
            return b"<mpd" in low or b"<?xml" in low
        except Exception:
            return False

    seen_mpd = set()
    for expected, mpd_url, pc, is_hdr, use_sdr in mpd_results:
        # HARD reject anything that is not pure MPD
        if not mpd_url:
            continue
        _raw_check = (mpd_url or "").split("|")[0].lower()
        if ".mpd" not in _raw_check or ".m3u8" in _raw_check:
            try:
                print(f"  {GRAY}· skip 4K MPD {expected} (not .mpd / is m3u8){RESET}")
            except Exception:
                pass
            continue
        pk = mpd_url.split("?")[0].lower()
        dkey = (pk, bool(is_hdr))
        if dkey in seen_mpd:
            continue
        seen_mpd.add(dkey)

        emb = mpd_url
        try:
            emb = _embed_fhd_hdntl(emb)
        except Exception:
            pass
        # After cookie embed, still must be .mpd
        if ".mpd" not in (emb or "").split("|")[0].lower() or ".m3u8" in (emb or "").lower():
            continue

        drm_details = {}
        try:
            drm_details = _fetch_drm_details(emb, pc or {}, slug_path=slug) or {}
        except Exception:
            drm_details = {}

        key_list = list((drm_details or {}).get("keys") or [])
        is_drm = bool((drm_details or {}).get("is_drm"))

        # Encrypted without keys → skip
        if is_drm and not key_list:
            try:
                print(f"  {GRAY}· skip 4K MPD {expected} (no DRM keys){RESET}")
            except Exception:
                pass
            continue

        if key_list:
            key_str = ",".join(key_list)
            tok = extract_hdntl_from_url(emb.split("|")[0]) or ""
            try:
                emb = _embed_drm_in_url(emb, key_str, tok)
            except Exception:
                pass

        if not _probe_mpd_reachable(emb):
            try:
                print(f"  {GRAY}· skip 4K MPD {expected} (URL not playable){RESET}")
            except Exception:
                pass
            continue

        # Final guard after all transforms
        if ".mpd" not in (emb or "").split("|")[0].lower() or ".m3u8" in (emb or "").lower():
            continue

        if is_hdr:
            ln = f"{expected} 4K HDR"
        else:
            ln = f"{expected} 4K SDR"

        # Same as FHD MPD: (30M) + (24H)
        entries.append((f"{ln} 30M", emb, bool(is_hdr), drm_details, emb))
        try:
            tok24 = get_24h_cookie_cached(force=False)
        except Exception:
            tok24 = ""
        if tok24:
            try:
                url24 = append_hdntl_cookie_to_url(emb.split("|")[0], tok24)
            except Exception:
                url24 = emb
            if ".mpd" in (url24 or "").split("|")[0].lower() and ".m3u8" not in (url24 or "").lower():
                if _probe_mpd_reachable(url24):
                    entries.append((f"{ln} 24H", url24, bool(is_hdr), drm_details, emb))
                else:
                    # still add 24H label with token (FHD MPD style) even if probe soft-fails
                    entries.append((f"{ln} 24H", url24, bool(is_hdr), drm_details, emb))

    n_mpd = sum(1 for e in entries if len(e) > 1 and ".mpd" in str(e[1]).lower())
    if n_mpd:
        try:
            print(f"  {GREEN}✓ 4K MPD streams (working .mpd only): {n_mpd}{RESET}")
        except Exception:
            pass
    return entries



def _embed_fhd_hdntl(url: str) -> str:
    """FHD: always ensure working Set-Cookie/API hdnea on URL (was missing → streams dead)."""
    raw = (url or "").split("|")[0].strip()
    if not raw:
        return url
    # Drop CF junk params
    try:
        parsed = urlparse(raw)
        kept = []
        for part in (parsed.query or "").split("&"):
            if not part:
                continue
            k = part.split("=", 1)[0].lower()
            if k in ("signature", "expires", "key-pair-id", "ttl"):
                continue
            kept.append(part)
        raw = urlunparse(parsed._replace(query="&".join(kept)))
    except Exception:
        pass
    existing = ""
    try:
        existing = extract_hdntl_from_url(raw) or ""
        existing = _strip_hdntl_prefix(existing) if existing else ""
    except Exception:
        existing = ""
    # Prefer fresh Set-Cookie for FHD (30M)
    token = ""
    try:
        token = get_hdntl_token_4kads(raw, retries=6) or ""
        token = _strip_hdntl_prefix(token) if token else ""
    except Exception:
        token = ""
    use = token or existing
    if use and "exp=" in use:
        return append_hdntl_to_url_4kads(raw, use)
    return raw


def fetch_event_fhd_entries(ev_title: str, ev_url: str, fast: bool = False) -> tuple:
    """Fetch NORMAL FHD (30 MIN) streams for one event.
    Returns (entries, logo_url). fast=True → eng+hin only, fewer retries (re-fetch path)."""
    slug = extract_slug_path(ev_url)
    if not slug:
        return [], ""
    raw_entries: dict = {}
    seen_bases:  set  = set()
    # Start with real images.h from legacy hotlive.php API when available
    logo_url = ""
    try:
        logo_url = lookup_legacy_logo(ev_title, ev_title, ev_url) or ""
    except Exception:
        logo_url = ""
    logo_done = bool(logo_url and "-h" in logo_url)

    lang_items = list(UNIQUE_LANGUAGES.items())
    # eng + hin first so sports MPD gets correct ENGLISH/HINDI label before regional noise
    def _lang_prio(item):
        lc = (item[0] or "").lower()
        if lc in ("eng", "en"): return 0
        if lc in ("hin", "hi"): return 1
        return 2
    lang_items.sort(key=_lang_prio)
    if fast:
        prefer = {"eng", "en", "hin", "hi"}
        lang_items = [(lc, ln) for lc, ln in lang_items if lc in prefer]
        if not lang_items:
            lang_items = list(UNIQUE_LANGUAGES.items())[:2]

    with ThreadPoolExecutor(max_workers=min(6, max(2, len(lang_items)))) as ex:
        futs = {
            ex.submit(fetch_lang_stream, lc, ln, slug, ev_url, "2", fast): ln
            for lc, ln in lang_items
        }
        for f in as_completed(futs):
            r = f.result()
            if not r:
                continue
            lname  = r["lang_name"] or futs[f]
            stream = r["stream"]
            # Real language priority:
            #   1) CDN path (/eng/, biggboss-hin-2026)
            #   2) player_config playback_tags language:
            #   3) API requested lang (last resort — often wrong for MPD sports)
            pc = r.get("player_config") or {}
            _lu = _lang_from_stream_url(stream, "")
            if _lu:
                lname = _lu
            else:
                _pt = str(pc.get("playback_tags") or "")
                _from_pc = ""
                for _tag in _pt.split(";"):
                    _t = _tag.strip()
                    if _t.lower().startswith("language:"):
                        _code = _t.split(":", 1)[1].strip().lower()
                        _from_pc = LANGUAGES.get(_code) or LANGUAGES.get(_code[:3]) or ""
                        if _from_pc:
                            break
                if _from_pc:
                    lname = _from_pc
                # else keep API lang name (lname)
            base   = stream.split("?")[0]
            is_mpd = ".mpd" in base.lower()
            if not lname:
                lname = "ENGLISH"
            # Dedupe by language + by path (MPD sports often return same eng package for every lang=)
            if lname in raw_entries:
                continue
            if base in seen_bases:
                # If we already stored a regional label for this eng package, upgrade to ENGLISH
                if is_mpd and lname == "ENGLISH":
                    for _old_ln in list(raw_entries.keys()):
                        if raw_entries[_old_ln][0].split("?")[0] == base and _old_ln != "ENGLISH":
                            raw_entries.pop(_old_ln, None)
                            raw_entries["ENGLISH"] = (
                                stream, r.get("is_hdr", False), pc
                            )
                            break
                continue
            seen_bases.add(base)
            raw_entries[lname] = (
                stream, r.get("is_hdr", False), pc
            )
            if not logo_done:
                pc = r.get("player_config") or {}
                logo_try = extract_logo_from_player_config(pc)
                if logo_try:
                    logo_url = logo_try
                    if "-h" in logo_try:
                        logo_done = True

    if not raw_entries:
        # still try real logo from API even if no streams
        if not logo_url or "-h" not in logo_url:
            try:
                logo_url = extract_logo_from_url(ev_url) or logo_url
            except Exception:
                pass
        return [], logo_url

    # Watch JSON often only has title_cutout(-t) + cast_image(-b) — no -h.
    # resolve_event_logo: legacy images.h → detail API → cast -b → other
    try:
        logo_url = resolve_event_logo(ev_title or "", ev_title or "", ev_url, logo_url or "")
    except Exception:
        pass
    if logo_url:
        logo_url = _hq_logo(logo_url)

    # Embed 30-min IP-bound hdnea token per URL (parallel) — FHD needs Set-Cookie
    with ThreadPoolExecutor(max_workers=len(raw_entries)) as emb_ex:
        emb_futs = {
            emb_ex.submit(_embed_fhd_hdntl, data[0]): ln
            for ln, data in raw_entries.items()
        }
        embedded: dict = {}
        for ef in as_completed(emb_futs):
            ln = emb_futs[ef]
            try:
                embedded[ln] = ef.result()
            except Exception:
                embedded[ln] = raw_entries[ln][0]

    entries = []
    for ln, (raw_url, is_hdr, player_config) in raw_entries.items():
        emb_url = embedded.get(ln, raw_url)
        # Rewrite live-cf.cdn.hotstar.com → live*.hotstar.com using playback_host param
        check_url = emb_url.split("|")[0] if "|" in emb_url else emb_url
        if "live-cf.cdn.hotstar.com" in check_url or "live-ssai-cf" in check_url or _is_bad_cf_token_url(check_url):
            rewritten = rewrite_cdn_to_livehost(check_url)
            if rewritten != check_url and not _is_bad_cf_token_url(rewritten):
                emb_url = rewritten
            else:
                continue
        # Always ensure token after rewrite
        if "hdnea=" not in emb_url.lower() and "hdntl=" not in emb_url.lower():
            emb_url = _embed_fhd_hdntl(emb_url)
        # Prefer livexx.hotstar.com / live-jiol.cdn.hotstar.com — already good hosts
        # (no rewrite needed)
        drm_details = _fetch_drm_details(emb_url, player_config, slug_path=slug)
        if drm_details.get("is_drm"):
            key_list = drm_details.get("keys") or []
            if key_list:
                key_str = ",".join(key_list)
                tok = extract_hdntl_from_url(emb_url.split("|")[0]) or ""
                emb_url = _embed_drm_in_url(emb_url, key_str, tok)
                _meth = drm_details.get("method") or "?"
                print(f"  {GREEN}✓ DRM keys for {ln} [{_meth}]:{RESET}")
                for _k in key_list:
                    print(f"    {CYAN}{_k}{RESET}")
            else:
                kids = drm_details.get("key_ids") or []
                why = drm_details.get("error") or "unknown"
                if kids:
                    print(f"  {YELLOW}⚠ DRM MPD for {ln} — KIDs={len(kids)} keys failed: {why}{RESET}")
                    if drm_details.get("license_url"):
                        print(f"    {GRAY}license: {drm_details['license_url'][:80]}...{RESET}")
                    else:
                        print(f"    {GRAY}license: (none){RESET}")
                    if "device.wvd" in why or "pywidevine" in why:
                        print(f"    {GRAY}→ place device.wvd next to script & pip install pywidevine{RESET}")
                else:
                    print(f"  {YELLOW}⚠ DRM MPD for {ln}, but no KIDs/keys available{RESET}")
        # MPD → dual streams: 30M (short cookie) + 24H (long cookie, SD tokens)
        is_mpd = ".mpd" in (emb_url or "").lower()
        if is_mpd:
            key_list = list((drm_details or {}).get("keys") or [])
            key_str = ",".join(key_list) if key_list else ""
            # 30M — existing embedded short cookie
            entries.append((f"{ln} 30M", emb_url, is_hdr, drm_details))
            # 24H — global long cookie (cached 5h, SD token pool)
            try:
                tok24 = get_24h_cookie_cached(force=False)
            except Exception:
                tok24 = ""
            if tok24:
                # Same M3U format as 30M: only swap hdnea cookie → 24H token (no pipe URL)
                url24 = append_hdntl_cookie_to_url(emb_url.split("|")[0], tok24)
                entries.append((f"{ln} 24H", url24, is_hdr, drm_details))
            else:
                # still add label so user sees 30M-only
                pass
        else:
            # 5th element = raw API URL (query hdnea ≈ 7–15 min, hot.py NORMAL FHD)
            entries.append((ln, emb_url, is_hdr, drm_details, raw_url))
    return entries, logo_url


def get_time_based_token_index(tokens: list) -> int:
    """Return token slot index based on current IST CYCLE_MINUTES boundary.
    Uses India Standard Time (UTC+5:30) so rotation is consistent in India."""
    if not tokens:
        return 0
    ist_minutes = int((time.time() + _IST_OFFSET_SEC) // 60)
    slot = (ist_minutes // CYCLE_MINUTES) % len(tokens)
    return slot


def seconds_until_next_cycle() -> float:
    """Seconds remaining until next CYCLE_MINUTES wall-clock boundary (IST)."""
    ist_epoch   = time.time() + _IST_OFFSET_SEC
    cycle_sec   = CYCLE_MINUTES * 60
    elapsed     = ist_epoch % cycle_sec
    return cycle_sec - elapsed


def push_to_cloudflare_fhd(filename: str, worker_url: str, api_token: str) -> bool:
    """Push M3U file to Cloudflare Worker (alias of push_to_cloudflare)."""
    return push_to_cloudflare(filename, worker_url, api_token)


# =========================
# COMBINED M3U BUILDER
# =========================
def build_combined_m3u(all_event_entries: list, filename: str) -> bool:
    """
    all_event_entries: [(title_line1, title_line2, logo_url,
                         [(lang, url, is_hdr), ...]), ...]
    """
    import hashlib
    try:
        with open(filename, "w", encoding="utf-8") as f:
            f.write("#EXTM3U\n")
            f.write("# Playlist generated by Hotstar Extractor\n")
            f.write("# Playlist Created By @rtxcric\n")
            f.write(f"# Mode: NORMAL FHD 30 MINUTES AUTO-UPDATE\n")
            f.write(f"# Generated: {datetime.now(IST).strftime('%Y-%m-%d %I:%M:%S %p')}\n\n")
            for event in all_event_entries:
                if len(event) == 4:
                    title_line1, title_line2, logo_url, entries = event
                else:
                    # Backward compatibility with the old (title, logo, entries) form.
                    title_line1, logo_url, entries = event
                    title_line2 = title_line1
                group_title = f"{title_line1}: {title_line2}"
                for entry in entries:
                    if len(entry) >= 4:
                        lang, url, is_hdr, drm_details = entry[:4]
                    else:
                        lang, url, is_hdr = entry[:3]
                        drm_details = {}
                    tvg_id = str(int(hashlib.md5(url.encode()).hexdigest(), 16) % 9999999999)
                    channel_label = f"{lang} FHD HDR" if is_hdr else f"{lang} FHD"
                    token_to_use = extract_hdntl_from_url(url) or ""
                    is_drm = bool(drm_details.get("is_drm"))
                    if logo_url:
                        f.write(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title_line2}" '
                                f'tvg-logo="{logo_url}" group-title="{group_title}", {channel_label} @rtxcric\n')
                    else:
                        f.write(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title_line2}" '
                                f'group-title="{group_title}", {channel_label} @rtxcric\n')
                    _drm_keys = list(drm_details.get("keys") or [])
                    if is_drm or ".mpd" in (url or "").lower():
                        f.write("#KODIPROP:inputstream.adaptive.manifest_type=mpd\n")
                        if _drm_keys:
                            f.write("#KODIPROP:inputstream.adaptive.license_type=clearkey\n")
                            # Prefer single combined key line (Kodi accepts kid:key pairs comma-joined)
                            f.write(f"#KODIPROP:inputstream.adaptive.license_key={','.join(_drm_keys)}\n")
                    # Also parse keys already embedded in pipe URL
                    if not _drm_keys:
                        _ck_m = re.search(r"(?:drmLicense|drm_license)=([0-9a-fA-F:,]+)", url or "")
                        if _ck_m:
                            _parsed = _ck_m.group(1).strip().rstrip("&|")
                            f.write("#KODIPROP:inputstream.adaptive.manifest_type=mpd\n")
                            f.write("#KODIPROP:inputstream.adaptive.license_type=clearkey\n")
                            f.write(f"#KODIPROP:inputstream.adaptive.license_key={_parsed}\n")
                    if not token_to_use:
                        _tok_m = re.search(r"(?:Cookie|cookie)=hdntl=([^&|]+)", url or "")
                        if _tok_m:
                            token_to_use = unquote(_tok_m.group(1).strip())
                    _exthttp = f'{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}"'
                    if token_to_use:
                        _exthttp += f',"Cookie":"hdntl={token_to_use}"'
                    _exthttp += '}'
                    f.write(f'#EXTHTTP:{_exthttp}\n')
                    if token_to_use:
                        f.write(f"#EXTVLCOPT:http-cookie=hdntl={token_to_use}\n")
                    f.write(f'#EXTVLCOPT:http-extra-headers=Origin: {M3U_ORIGIN}\n')
                    f.write(f'#EXTVLCOPT:http-referrer={M3U_REFERER}\n')
                    f.write(f'#EXTVLCOPT:http-user-agent={M3U_USER_AGENT}\n')
                    f.write(f"{url}\n")
        return True
    except Exception as e:
        print(f"{RED}M3U write error: {e}{RESET}")
        return False


# =========================
# H.PY-STYLE HDNTL REFRESH (no user tokens — real CDN Set-Cookie only)
# =========================
HOTSTAR_UA_REFRESH = "Hotstar;in.startv.hotstar/25.02.24.8.11169@rtxcric(Android/15)"
HOTSTAR_REFERER_R  = "https://www.hotstar.com/"
HOTSTAR_ORIGIN_R   = "https://www.hotstar.com"


def _hdntl_from_text(value: str) -> str:
    if not isinstance(value, str) or "hdntl" not in value.lower():
        return ""
    match = re.search(
        r"(?:^|[?&;,\s|])(?:Cookie=)?hdntl=([^;,\s&|\"'<>\r\n]+)",
        value,
        flags=re.IGNORECASE,
    )
    return match.group(1).strip() if match else ""


def _hdntl_from_response(response) -> str:
    try:
        raw = response.headers.get("Set-Cookie", "") or ""
    except Exception:
        raw = ""
    token = _hdntl_from_text(raw)
    if token:
        return token
    try:
        location = response.headers.get("Location", "") or ""
    except Exception:
        location = ""
    return _hdntl_from_text(location)


def _hdntl_expiry(hdntl: str) -> int:
    match = re.search(r"(?:^|~)exp=(\d+)", hdntl or "", flags=re.IGNORECASE)
    return int(match.group(1)) if match else 0


def _looks_like_real_hdntl(hdntl: str) -> bool:
    if not hdntl or len(hdntl) < 40:
        return False
    if not re.search(r"(?:^|~)exp=\d+", hdntl, re.IGNORECASE):
        return False
    exp = _hdntl_expiry(hdntl)
    return exp > int(time.time()) + 60


def _fresh_refresh_headers() -> dict:
    """Brand-new random device + request IDs for every CDN cookie probe (h.py style)."""
    ua, client, app_code = _get_android_device()
    return {
        "User-Agent": ua,
        "Referer": HOTSTAR_REFERER_R,
        "Origin": HOTSTAR_ORIGIN_R,
        "Accept": "*/*",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
        "X-HS-Platform": "android",
        "X-Country-Code": "in",
        "X-HS-Client": client,
        "x-hs-app": app_code,
        "X-Request-Id": str(uuid.uuid4()),
        "x-hs-request-id": str(uuid.uuid4()),
        "x-hs-device-id": str(uuid.uuid4()),
    }


def fetch_hdntl_from_existing_url(url: str, retries: int = 6) -> str:
    """
    h.py-style guest CDN Set-Cookie refresh (NO user tokens).
    Uses proxy so IP matches stream playback.
    Order: original URL → rewritten livehost → https → parent path.
    """
    base_url = (url or "").split("|", 1)[0].strip()
    if not base_url.startswith("http"):
        return ""

    old_token = ""
    try:
        old_token = extract_hdntl_from_url(base_url) or ""
        old_token = _strip_hdntl_prefix(old_token) if old_token else ""
    except Exception:
        old_token = ""
    if not old_token:
        m = re.search(r"(?:^|[?&|])(?:hdnea|hdntl)=([^;,\s&|\"'\n]+)", base_url, flags=re.I)
        if m:
            try:
                old_token = _strip_hdntl_prefix(m.group(1))
            except Exception:
                old_token = m.group(1)

    # Build probe URL list — original FIRST (do not force rewrite)
    request_urls = []
    def _add(u):
        u = (u or "").strip()
        if u and u not in request_urls:
            request_urls.append(u)

    _add(base_url)
    # strip token for clean probe
    try:
        parts = urlparse(base_url)
        qparts = []
        for item in (parts.query.split("&") if parts.query else []):
            key = item.split("=", 1)[0].lower()
            if key not in {"hdntl", "hdnea"}:
                qparts.append(item)
        clean = urlunparse((parts.scheme, parts.netloc, parts.path, "", "&".join(qparts), ""))
        _add(clean)
    except Exception:
        clean = base_url
    # rewritten live host variant
    try:
        rw = rewrite_cdn_to_livehost(base_url) or ""
        if rw:
            _add(rw)
            parts2 = urlparse(rw)
            q2 = []
            for item in (parts2.query.split("&") if parts2.query else []):
                key = item.split("=", 1)[0].lower()
                if key not in {"hdntl", "hdnea"}:
                    q2.append(item)
            _add(urlunparse((parts2.scheme, parts2.netloc, parts2.path, "", "&".join(q2), "")))
    except Exception:
        pass
    # https upgrade
    for u in list(request_urls):
        if u.startswith("http://"):
            _add("https://" + u[len("http://"):])
    # parent folder
    try:
        parts = urlparse(base_url)
        if parts.path and ("master" in parts.path or parts.path.endswith(".m3u8")):
            parent = parts.path.rsplit("/", 1)[0] + "/"
            _add(urlunparse((parts.scheme, parts.netloc, parent, "", "", "")))
    except Exception:
        pass

    def _ok(tok: str) -> bool:
        if not tok or not _looks_like_real_hdntl(tok):
            return False
        if tok != old_token:
            return True
        try:
            return _hdntl_ttl_left(tok) > 180
        except Exception:
            return False

    def _probe(request_url: str, send_cookie: bool = True) -> str:
        headers = _fresh_refresh_headers()  # guest device — no user token
        if send_cookie and old_token:
            headers = dict(headers)
            headers["Cookie"] = f"hdntl={old_token}"
        req = request.Request(request_url, headers=headers, method="GET")
        # proxy via global opener (install_opener in _init_proxy)
        try:
            with request.urlopen(req, timeout=15) as response:
                token = _hdntl_from_response(response)
                if _ok(token):
                    return _strip_hdntl_prefix(token)
                get_all = getattr(response.headers, "get_all", None)
                if get_all:
                    for cookie in get_all("Set-Cookie") or []:
                        token = _hdntl_from_text(cookie)
                        if _ok(token):
                            return _strip_hdntl_prefix(token)
        except urllib.error.HTTPError as error:
            token = _hdntl_from_response(error)
            if _ok(token):
                return _strip_hdntl_prefix(token)
        except Exception:
            pass
        return ""

    for attempt in range(max(1, retries)):
        for request_url in request_urls:
            # 1) pure guest (no old cookie) — classic h.py
            tok = _probe(request_url, send_cookie=False)
            if tok:
                return tok
            # 2) re-issue with old cookie
            tok = _probe(request_url, send_cookie=True)
            if tok:
                return tok
        if attempt < retries - 1:
            time.sleep(0.35 + attempt * 0.25)

    # Keep existing guest token if still valid
    try:
        if old_token and _looks_like_real_hdntl(old_token) and _hdntl_ttl_left(old_token) > 90:
            return old_token
    except Exception:
        pass
    return ""



def replace_token_in_block(block: str, new_token: str) -> str:
    """Replace hdntl/hdnea in one #EXTINF block (URL + cookie directives)."""
    if not new_token:
        return block
    updated = re.sub(
        r"(cookie=hdntl=)[^\s&|\"'\n]+",
        lambda m: m.group(1) + new_token,
        block,
        flags=re.IGNORECASE,
    )
    updated = re.sub(
        r"(?<![=a-zA-Z])hdntl=(?!{)[^\s&|\"'\n]+",
        "hdntl=" + new_token,
        updated,
        flags=re.IGNORECASE,
    )
    updated = re.sub(
        r"(?<![=a-zA-Z])hdnea=(?!{)[^\s&|\"'\n]+",
        "hdnea=" + new_token,
        updated,
        flags=re.IGNORECASE,
    )
    return updated


def refresh_7m_cookies_in_m3u(content: str, event_state: dict, active_token: str = "") -> tuple:
    """
    Refresh (7M) streams with short API query hdnea (hot.py NORMAL FHD).
    NOT Set-Cookie 30m. Returns (new_content, updated_count, failed_count).
    """
    global _ACTIVE_TOKEN_OVERRIDE
    if "(7M)" not in (content or ""):
        return content, 0, 0

    lines = content.splitlines(keepends=True)
    seven_targets = []
    i = 0
    while i < len(lines):
        s = lines[i]
        if "(7M)" in s and s.lstrip().startswith("#EXTINF"):
            j = i + 1
            while j < len(lines) and not lines[j].strip().startswith("http"):
                j += 1
            if j < len(lines) and lines[j].strip().startswith("http"):
                gt = ""
                m = re.search(r'group-title="([^"]+)"', s)
                if m:
                    gt = m.group(1)
                # SKIP 24H / 24X7 / ttl=86400 streams
                if "24H" in gt or "24X7" in gt or "24/7" in gt:
                    i = j + 1
                    continue
                # Also check URL
                if is_24h_stream_url(lines[j].strip()):
                    i = j + 1
                    continue
                # SKIP 4K — 7M FHD refresh strips playback_host + breaks path-ACL
                if (
                    "4K" in s
                    or "4kssai" in lines[j].lower()
                    or "4khdr" in lines[j].lower()
                    or "/out/v1/" in lines[j].lower()
                ):
                    i = j + 1
                    continue
                seven_targets.append((j, lines[j].strip(), gt))
            i = j + 1
            continue
        i += 1

    if not seven_targets:
        return content, 0, 0

    src_by_gt = {}
    for key, meta in (event_state or {}).items():
        src = meta.get("source_url") or ""
        if not src:
            continue
        t1 = meta.get("title1") or ""
        t2 = meta.get("title2") or ""
        if t1 and t2:
            src_by_gt[f"{t1}: {t2}"] = src
            src_by_gt[f"{t1}|{t2}"] = src
        src_by_gt[key] = src
        if t2:
            src_by_gt[t2] = src

    fetch_jobs = {}
    unmatched = 0
    for idx, url, gt in seven_targets:
        src = src_by_gt.get(gt) or ""
        if not src:
            for k, v in src_by_gt.items():
                if gt and (gt in k or k in gt):
                    src = v
                    break
        if not src:
            unmatched += 1
            continue
        fetch_jobs.setdefault(src, []).append((idx, url, gt))

    if not fetch_jobs:
        return content, 0, len(seven_targets)

    updated = 0
    failed = unmatched
    prev_tok = _ACTIVE_TOKEN_OVERRIDE
    if active_token:
        _ACTIVE_TOKEN_OVERRIDE = active_token

    try:
        for src_url, targets in fetch_jobs.items():
            try:
                entries, _logo = fetch_event_fhd_entries("", src_url, fast=True)
            except Exception:
                failed += len(targets)
                continue
            by_lang = {}
            for entry in entries or []:
                if len(entry) >= 5:
                    lang, emb, is_hdr, drm, raw_u = entry[:5]
                elif len(entry) >= 4:
                    lang, emb, is_hdr, drm = entry[:4]
                    raw_u = emb
                else:
                    continue
                base_lang = re.sub(r"\s*(30M|24H|7M).*$", "", str(lang)).strip().upper()
                raw_tok = extract_hdntl_from_url((raw_u or "").split("|")[0]) or ""
                try:
                    raw_tok = _strip_hdntl_prefix(raw_tok)
                except Exception:
                    pass
                if raw_tok:
                    by_lang[base_lang] = (raw_u or emb, raw_tok)

            if not by_lang:
                failed += len(targets)
                continue

            for idx, old_url, gt in targets:
                lang_guess = ""
                low = old_url.lower()
                for code, name in [
                    ("/eng/", "ENGLISH"), ("/hin/", "HINDI"), ("/tam/", "TAMIL"),
                    ("/tel/", "TELUGU"), ("/kan/", "KANNADA"), ("/mal/", "MALAYALAM"),
                    ("/ben/", "BENGALI"), ("/mar/", "MARATHI"), ("/guj/", "GUJARATI"),
                    ("/pan/", "PUNJABI"),
                ]:
                    if code in low:
                        lang_guess = name
                        break
                pair = by_lang.get(lang_guess) if lang_guess else None
                if not pair:
                    pair = next(iter(by_lang.values()), None)
                if not pair or not pair[1]:
                    failed += 1
                    continue
                raw_u, raw_tok = pair
                base = old_url.split("|")[0].split("?")[0]
                try:
                    new_url = append_hdntl_to_url_4kads(base, raw_tok)
                except Exception:
                    new_url = f"{base}?a=ns&hdnea={raw_tok}"
                ends = ""
                if lines[idx].endswith("\r\n"):
                    ends = "\r\n"
                elif lines[idx].endswith("\n"):
                    ends = "\n"
                lines[idx] = new_url + ends
                updated += 1
    finally:
        _ACTIVE_TOKEN_OVERRIDE = prev_tok

    return "".join(lines), updated, failed



def _refresh_low_ttl_4k_via_api(event_state: dict, m3u_file: str) -> int:
    """
    4K path-ACL tokens expire ~30m — guest Set-Cookie breaks them.
    Re-fetch from API when TTL < 20 min or last fetch > 18 min.
    """
    if not event_state:
        return 0
    need = []
    now = time.time()
    for key, meta in list(event_state.items()):
        has_4k = False
        low = False
        for blk in (meta.get("blocks") or []):
            if "4K" not in blk and "4kssai" not in blk and "/out/v1/" not in blk:
                continue
            has_4k = True
            for ln in blk.splitlines():
                s = ln.strip()
                if not s.startswith("http"):
                    continue
                try:
                    tok = extract_hdntl_from_url(s) or ""
                    tok = _strip_hdntl_prefix(tok) if tok else ""
                    left = _hdntl_ttl_left(tok) if tok else 0
                except Exception:
                    left = 0
                if left < 1200:
                    low = True
                    break
            if low:
                break
        if not has_4k:
            continue
        age = now - float(meta.get("last_refetch") or meta.get("added_at") or meta.get("last_seen") or 0)
        if low or age > 18 * 60 or age <= 0:
            need.append((key, meta))

    if not need:
        return 0

    n_ok = 0
    for key, meta in need:
        t1 = meta.get("title1") or ""
        t2 = meta.get("title2") or ""
        source_url = meta.get("source_url") or ""
        if not source_url:
            continue
        print(f"  {DARK_MAGENTA}↻ 4K cookie refresh (keep URL): {t2[:55]}{RESET}")
        # Do NOT re-fetch 4K stream URLs — only refresh hdnea on existing lines
        new_blocks = []
        refreshed = 0
        for blk in (meta.get("blocks") or []):
            lines = blk.splitlines()
            out_lines = []
            i = 0
            while i < len(lines):
                line = lines[i]
                s = line.strip()
                is_4k_line = (
                    "4K" in blk
                    or "4kssai" in s.lower()
                    or "4khdr" in s.lower()
                    or "/out/v1/" in s.lower()
                )
                if s.startswith("http") and is_4k_line:
                    try:
                        new_u = _embed_hdntl_in_url(s) or s
                        if new_u and new_u != s:
                            refreshed += 1
                        out_lines.append(new_u if new_u else s)
                    except Exception:
                        out_lines.append(s)
                else:
                    out_lines.append(line)
                i += 1
            new_blocks.append("\n".join(out_lines))
        if refreshed:
            meta["blocks"] = new_blocks
            meta["last_refetch"] = time.time()
            n_ok += 1
        if refreshed:
            print(f"  {GREEN}✓ 4K cookie refresh: {refreshed} URL(s){RESET}")

    if n_ok:
        rebuild_m3u_from_events(event_state, m3u_file)
    return n_ok



def _acl_path_from_token(tok: str) -> str:
    """Return decoded acl path from hdnea/hdntl token (without trailing *)."""
    if not tok:
        return ""
    try:
        m = re.search(r"acl=([^~&]+)", tok, flags=re.I)
        if not m:
            return ""
        acl = unquote(m.group(1)).strip()
        if acl.endswith("*"):
            acl = acl[:-1]
        return acl
    except Exception:
        return ""


def _token_matches_stream_url(tok: str, url: str) -> bool:
    """True if token path-ACL matches URL path (or wildcard /*)."""
    acl = _acl_path_from_token(tok)
    if not acl:
        return False
    if acl in ("/*", "/", "*"):
        return False  # never accept guest /* for 4K
    try:
        path = urlparse(url).path or ""
        if path.startswith(acl) or acl.rstrip("/") in path:
            return True
        if "/out/v1/" in path and "/out/v1/" in acl:
            p_parts = [x for x in path.split("/") if x]
            a_parts = [x for x in acl.split("/") if x]
            if len(p_parts) >= 4 and len(a_parts) >= 4:
                if p_parts[:4] == a_parts[:4]:
                    return True
        if "/cmaf/" in path and "/cmaf/" in acl:
            pm = re.search(r"/cmaf/live/(\d+)/", path)
            am = re.search(r"/cmaf/live/(\d+)/", acl)
            if pm and am and pm.group(1) == am.group(1):
                return True
    except Exception:
        return False
    return False


def _lang_code_from_4k_url(url: str) -> str:
    low = (url or "").lower()
    for code, name in [
        ("/eng/", "eng"), ("/hin/", "hin"), ("/tam/", "tam"),
        ("/tel/", "tel"), ("/kan/", "kan"), ("/mal/", "mal"),
        ("/ben/", "ben"), ("/mar/", "mar"), ("/guj/", "guj"),
        ("/pan/", "pan"), ("/bho/", "bho"), ("/har/", "har"),
        ("english", "eng"), ("hindi", "hin"),
    ]:
        if code in low:
            return name
    return "eng"


def _is_4k_hdr_url(url: str) -> bool:
    low = (url or "").lower()
    return "4khdr" in low or "hdr10" in low or "dr%3Dhdr" in low or "dr=hdr" in low


def _fetch_4k_7m_fresh_url(stream_url: str, source_url: str = "") -> str:
    """Return a full fresh 4K (7M) URL from BFF API (path + short path-ACL together).
    Never paste a foreign ACL onto an old path — that breaks playback.
    """
    if not stream_url:
        return ""
    slug = ""
    if source_url:
        try:
            slug = extract_slug_path(source_url) or ""
        except Exception:
            slug = ""
    if not slug:
        return ""
    lang = _lang_code_from_4k_url(stream_url)
    use_sdr = not _is_4k_hdr_url(stream_url)
    codes = [lang]
    for _k, v in (LANG_MAP_4KADS or {}).items():
        if lang in v or (v and v[0] == lang):
            codes = list(v)
            break
    expected = LANG_DISPLAY_4KADS.get(lang, lang.upper())
    try:
        fresh = fetch_stream_4kads_lite(
            slug, codes, expected, use_sdr=use_sdr, max_retries=10,
            prefer_out_v1_4k=(lang in ("eng", "hin")),
        )
    except Exception:
        fresh = ""
    if not fresh or ".m3u8" not in fresh:
        return ""
    # Ensure token present + path-ACL matches THIS fresh URL
    try:
        tok = extract_hdntl_from_url(fresh) or ""
        tok = _strip_hdntl_prefix(tok) if tok else ""
        if not tok or "exp=" not in tok:
            # embed short/API token onto fresh URL only
            try:
                t2 = _fetch_short_hdntl_for_url(fresh) or get_hdntl_token_4kads(fresh, retries=3) or ""
                t2 = _strip_hdntl_prefix(t2) if t2 else ""
                if t2 and _token_matches_stream_url(t2, fresh):
                    return append_hdntl_to_url_4kads(fresh, t2)
            except Exception:
                pass
            return fresh
        if _token_matches_stream_url(tok, fresh):
            return fresh
        # token mismatch on fresh — try short probe
        t3 = _fetch_short_hdntl_for_url(fresh) or ""
        t3 = _strip_hdntl_prefix(t3) if t3 else ""
        if t3 and _token_matches_stream_url(t3, fresh):
            return append_hdntl_to_url_4kads(fresh, t3)
        return fresh
    except Exception:
        return fresh


def refresh_4k_cookies_in_m3u(content: str, event_state: dict = None) -> tuple:
    """Refresh 4K cookies.
    (7M)         → full fresh API URL (short path-ACL, path always matches)
    (30M STABLE) → same URL + CDN Set-Cookie (~30 min) if ACL matches
    Returns (content, updated, failed).
    """
    if not content or "4K" not in content:
        return content, 0, 0
    lines = content.splitlines(keepends=True)
    src_by_cid = {}
    for _k, meta in (event_state or {}).items():
        su = (meta or {}).get("source_url") or ""
        if not su:
            continue
        cid = _content_id_from_url(su)
        if cid:
            src_by_cid[cid] = su
        for blk in (meta or {}).get("blocks") or []:
            for ln in blk.splitlines():
                if ln.strip().startswith("http"):
                    c2 = _content_id_from_url(ln)
                    if c2:
                        src_by_cid[c2] = su

    targets = []
    for i, line in enumerate(lines):
        s = line.strip()
        if not s.startswith("http"):
            continue
        label = ""
        for j in range(i - 1, max(-1, i - 20), -1):
            if lines[j].lstrip().startswith("#EXTINF"):
                label = lines[j]
                break
        if "4K" not in label and "4kssai" not in s.lower() and "/out/v1/" not in s.lower():
            continue
        # 4K: only (30M STABLE) — skip any leftover (7M)
        if "(7M)" in label:
            continue
        targets.append((i, s, "30M"))
    if not targets:
        return content, 0, 0

    updated = 0
    failed = 0

    def _one(item):
        idx, u, tag = item
        try:
            # 30M STABLE only — Set-Cookie on SAME url, ACL must match
            tok = get_hdntl_token_4kads(u, retries=6) or ""
            tok = _strip_hdntl_prefix(tok) if tok else ""
            if not tok or "exp=" not in tok:
                return idx, ""
            if not _token_matches_stream_url(tok, u):
                return idx, ""
            return idx, append_hdntl_to_url_4kads(u, tok)
        except Exception:
            return idx, ""

    results = {}
    # fewer workers — 7M does full API fetch per lang
    with ThreadPoolExecutor(max_workers=min(3, max(1, len(targets)))) as ex:
        futs = [ex.submit(_one, t) for t in targets]
        for f in as_completed(futs):
            idx, new_u = f.result()
            results[idx] = new_u

    for index in sorted(results.keys(), reverse=True):
        new_u = results[index]
        if not new_u:
            failed += 1
            continue
        start_i = 0
        for i in range(index, -1, -1):
            if lines[i].lstrip().startswith("#EXTINF"):
                start_i = i
                break
        end_i = len(lines)
        for i in range(index + 1, len(lines)):
            if lines[i].lstrip().startswith("#EXTINF"):
                end_i = i
                break
        tok = extract_hdntl_from_url(new_u) or ""
        tok = _strip_hdntl_prefix(tok) if tok else ""
        if tok:
            block = "".join(lines[start_i:end_i])
            new_block = replace_token_in_block(block, tok)
            blines = new_block.splitlines(keepends=True)
        else:
            blines = lines[start_i:end_i]
        out = []
        for bl in blines:
            if bl.strip().startswith("http"):
                out.append(new_u + "\n")
            else:
                out.append(bl if bl.endswith("\n") else bl + "\n")
        lines[start_i:end_i] = out
        updated += 1

    return "".join(lines), updated, failed


def refresh_all_hdntl_in_m3u(content: str) -> tuple:
    """
    For every URL that already has hdntl/hdnea, request a fresh Set-Cookie
    and replace only that entry. Returns (new_content, updated_count, failed_count, failed_urls).
    """
    lines = content.splitlines(keepends=True)
    targets = []
    for index, line in enumerate(lines):
        s = line.strip()
        if not s.startswith("http"):
            continue
        lower = s.lower()
        if not any(x in lower for x in ("hotstar.com", "jcevents", "cdn.hotstar")):
            continue
        if "hdntl=" in lower or "hdnea=" in lower:
            # Skip only true 24H long-cookie streams (not LIVE SHOW 30M under group "24/7")
            if is_24h_stream_url(s):
                continue
            skip_special = False
            for back in range(index - 1, max(-1, index - 14), -1):
                prev = lines[back]
                # Only skip if THIS channel is labeled (24H) / 24X7 stream — NOT group-title "24/7"
                if prev.lstrip().startswith("#EXTINF"):
                    # channel label is after the last comma
                    label = prev.split(",")[-1] if "," in prev else prev
                    if (
                        "(24H)" in label
                        or "(24X7)" in label
                        or re.search(r"\b24H\b", label)
                        or re.search(r"\b24X7\b", label)
                    ):
                        skip_special = True
                    break
                if prev.lstrip().startswith("http"):
                    break
            if skip_special:
                continue
            # Skip 4K — path-ACL hdnea must stay (guest acl=/* breaks playback)
            _blk_prev = ""
            for _pi in range(index, max(-1, index - 24), -1):
                if lines[_pi].lstrip().startswith("#EXTINF"):
                    _blk_prev = lines[_pi]
                    break
            sl = s.lower()
            if (
                "4K" in _blk_prev
                or "4kssai" in sl
                or "4khdr" in sl
                or "/out/v1/" in sl
            ):
                continue
            targets.append((index, s))

    if not targets:
        return content, 0, 0, []

    updated = 0
    failed = 0
    failed_urls = []
    # fewer parallel probes → less CDN rate-limit; more retries per URL
    workers = min(4, max(1, len(targets)))

    def _one(idx_url):
        idx, u = idx_url
        # 1) guest Set-Cookie refresh (h.py) — NEW guest token
        try:
            tok = fetch_hdntl_from_existing_url(u, retries=6)
            if _looks_like_real_hdntl(tok):
                return idx, u, tok, "new_guest"
        except Exception:
            pass
        # 2) keep existing token if still valid
        try:
            old_tok = extract_hdntl_from_url(u) or ""
            old_tok = _strip_hdntl_prefix(old_tok) if old_tok else ""
            if old_tok and _looks_like_real_hdntl(old_tok) and _hdntl_ttl_left(old_tok) > 60:
                return idx, u, old_tok, "kept"
        except Exception:
            pass
        return idx, u, "", "fail"

    results = {}
    n_new_guest = 0
    n_kept = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(_one, t) for t in targets]
        for f in as_completed(futs):
            idx, u, tok, how = f.result()
            results[idx] = (u, tok, how)
            if how == "new_guest":
                n_new_guest += 1
            elif how == "kept":
                n_kept += 1

    # Apply replacements from bottom to top so indices stay valid
    for index in sorted(results.keys(), reverse=True):
        url, new_hdntl, how = results[index]
        if not new_hdntl:
            failed += 1
            failed_urls.append(url)
            continue
        # Find #EXTINF block bounds
        start = 0
        for i in range(index, -1, -1):
            if lines[i].lstrip().startswith("#EXTINF"):
                start = i
                break
        end = len(lines)
        for i in range(index + 1, len(lines)):
            if lines[i].lstrip().startswith("#EXTINF"):
                end = i
                break
        block = "".join(lines[start:end])
        new_block = replace_token_in_block(block, new_hdntl)
        lines[start:end] = new_block.splitlines(keepends=True)
        updated += 1

    # Guest token summary (visible in cycle log)
    try:
        print(f"  {GRAY}· guest tokens: {n_new_guest} new Set-Cookie, {n_kept} kept existing{RESET}")
    except Exception:
        pass

    # Update header timestamp
    new_content = "".join(lines)
    now = datetime.now(IST).strftime("%Y-%m-%d %I:%M:%S %p")
    new_content = re.sub(
        r"(?m)^# Generated:.*$",
        f"# Generated: {now}",
        new_content,
    )
    new_content = re.sub(
        r"(?m)^# Mode:.*$",
        f"# Mode: FHD LIVE + HDNTL REFRESH (1 min) · grace {EVENT_GRACE_MINUTES}m",
        new_content,
    )
    return new_content, updated, failed, failed_urls


# =========================
# M3U EVENT STATE HELPERS
# =========================
def _content_id_from_url(url: str) -> str:
    """Last long numeric id in path — distinguishes same-titled LIVE SHOW feeds."""
    ids = re.findall(r"/(\d{5,})(?:/|$)", (url or "").split("?")[0])
    return ids[-1] if ids else ""


def _normalize_event_key(title1: str, title2: str, url: str = "") -> str:
    """Stable key for same live match across API title variations.

    Prefer match name (title2). For LIVE SHOW / LIVE EPISODE same-title feeds
    (e.g. BBS10 Tamil vs Telugu), append contentId so both stay separate.
    Sports matches with two feeds (same title, different contentId) collapse
    to ONE key so playlist is not duplicated.
    """
    t2 = (title2 or "").strip()
    t1 = (title1 or "").strip()
    primary = t2 or t1
    if primary.count(":") >= 2:
        parts = [p.strip() for p in primary.split(":") if p.strip()]
        if len(parts) >= 2:
            primary = f"{parts[-2]}: {parts[-1]}"
    primary = re.sub(r"^(bwf|icc|ipl|kcl|etpl|wpl)\s*\d{4}\s*:\s*", "", primary, flags=re.I)
    primary = re.sub(r"\s+", " ", primary).strip().lower()
    # strip trailing "by @rtxcric" if present from group titles
    primary = re.sub(r"\s*by\s*@rtxcric\s*$", "", primary, flags=re.I).strip()
    t1n = re.sub(r"\s+", " ", t1).strip().lower()
    t1n = re.sub(r"\s*by\s*@rtxcric\s*$", "", t1n, flags=re.I).strip()
    if t1n and t1n in primary:
        base = primary
    elif primary and primary in t1n:
        base = t1n
    else:
        base = primary or t1n
    # LIVE SHOW / EPISODE: keep contentId so Tamil vs Telugu both stay
    kind = (t1 or "").upper()
    is_show_family = (
        "LIVE SHOW" in kind or "LIVE EPISODE" in kind
        or "24x7" in base or "24 hrs" in base or "deferred" in base
        or base.startswith("bbs") or base.startswith("bb:")
    )
    cid = _content_id_from_url(url)
    if is_show_family and cid:
        return f"{base}|{cid}"
    # Sports / other: title-only key → one entry even if API returns 2 contentIds
    return base



def _state_content_ids(event_state: dict) -> dict:
    """Map contentId -> event_state key (from source_url)."""
    out = {}
    for k, meta in (event_state or {}).items():
        cid = _content_id_from_url(meta.get("source_url") or "")
        if cid:
            out[cid] = k
        # also from key suffix "|12345"
        if "|" in str(k):
            tail = str(k).rsplit("|", 1)[-1]
            if tail.isdigit() and len(tail) >= 5:
                out[tail] = k
    return out


def _live_event_present(event_state: dict, title1: str, title2: str, url: str) -> str:
    """Return existing event_state key if this live event is already tracked."""
    cid = _content_id_from_url(url)
    by_cid = _state_content_ids(event_state)
    if cid and cid in by_cid:
        return by_cid[cid]
    want = _normalize_event_key(title1, title2, url)
    if want in event_state:
        return want
    # unique title fallback (sports / single BBS titles)
    t2n = _normalize_event_key("", title2, "")
    matches = []
    for k, meta in event_state.items():
        if _normalize_event_key("", meta.get("title2") or "", "") == t2n:
            matches.append(k)
    if len(matches) == 1 and not cid:
        return matches[0]
    return ""


def _merge_state_after_parse(old_state: dict, new_state: dict) -> dict:
    """Preserve source_url / timers after M3U re-parse; re-key by contentId when possible."""
    if not old_state:
        return new_state
    # index old by contentId
    old_by_cid = {}
    for k, meta in old_state.items():
        cid = _content_id_from_url(meta.get("source_url") or "")
        if not cid and "|" in str(k):
            tail = str(k).rsplit("|", 1)[-1]
            if tail.isdigit():
                cid = tail
        if cid:
            old_by_cid[cid] = meta
    out = {}
    used_old = set()
    for k, meta in new_state.items():
        cid = _content_id_from_url(meta.get("source_url") or "")
        if not cid and "|" in str(k):
            tail = str(k).rsplit("|", 1)[-1]
            if tail.isdigit():
                cid = tail
        old = None
        if cid and cid in old_by_cid:
            old = old_by_cid[cid]
        elif k in old_state:
            old = old_state[k]
        if old:
            used_old.add(id(old))
            meta["source_url"] = old.get("source_url") or meta.get("source_url")
            meta["last_seen"] = old.get("last_seen", meta.get("last_seen"))
            meta["missing_since"] = old.get("missing_since")
            meta["refresh_fail_since"] = old.get("refresh_fail_since")
            meta["last_refetch"] = old.get("last_refetch")
            if old.get("logo") and not meta.get("logo"):
                meta["logo"] = old.get("logo")
            # prefer stable key from old source_url contentId
            src = meta.get("source_url") or ""
            if src:
                nk = _normalize_event_key(meta.get("title1") or "", meta.get("title2") or "", src)
                out[nk] = meta
                continue
        out[k] = meta
    # keep any old entries not represented (should be rare)
    for k, meta in old_state.items():
        if id(meta) in used_old:
            continue
        cid = _content_id_from_url(meta.get("source_url") or "")
        already = False
        if cid:
            for m in out.values():
                if _content_id_from_url(m.get("source_url") or "") == cid:
                    already = True
                    break
        if not already and k not in out:
            out[k] = meta
    return out


def parse_m3u_events(content: str) -> dict:
    """
    Parse existing M3U into {event_key: {title1, title2, logo, blocks: [str], last_seen}}.
    Each 'block' is the full text of one #EXTINF entry (directives + URL).
    """
    events = {}
    lines = content.splitlines(keepends=True)
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.lstrip().startswith("#EXTINF"):
            # Extract group-title and tvg-name / logo
            m_gt = re.search(r'group-title="([^"]*)"', line)
            m_name = re.search(r'tvg-name="([^"]*)"', line)
            m_logo = re.search(r'tvg-logo="([^"]*)"', line)
            group = m_gt.group(1) if m_gt else ""
            tvg_name = m_name.group(1) if m_name else ""
            logo = m_logo.group(1) if m_logo else ""
            # Category groups (LIVE TV / LIVE SHOW) share group-title —
            # identity is tvg-name, not the shared "24/7" suffix.
            gu = group.upper()
            if gu.startswith("LIVE TV") or gu.startswith("LIVE SHOW") or gu.startswith("LIVE EPISODE"):
                title1 = group
                title2 = tvg_name or group
            elif ": " in group:
                title1, title2 = group.split(": ", 1)
            else:
                title1, title2 = group, tvg_name or group
            # Collect full block until next #EXTINF or EOF
            start = i
            i += 1
            while i < len(lines) and not lines[i].lstrip().startswith("#EXTINF"):
                i += 1
            block = "".join(lines[start:i])
            # Prefer contentId from stream URL so same-titled LIVE SHOW stay separate
            block_url = ""
            hs_cid = ""
            for _bl in block.splitlines():
                sbl = _bl.strip()
                if sbl.startswith("http"):
                    block_url = sbl
                elif sbl.startswith("#HS-CID:"):
                    hs_cid = sbl.split(":", 1)[-1].strip()
            # Prefer page contentId from #HS-CID so key matches live API key
            key_url = block_url
            if hs_cid:
                key_url = f"https://www.hotstar.com/in/x/{hs_cid}/live/watch"
            # Normalize LIVE SHOW category title1 back to "LIVE SHOW"
            if (title1 or "").upper().startswith("LIVE SHOW"):
                title1 = "LIVE SHOW"
            key = _normalize_event_key(title1, title2, key_url)
            if key not in events:
                events[key] = {
                    "title1": title1,
                    "title2": title2,
                    "logo": logo,
                    "blocks": [],
                    "last_seen": time.time(),
                    "missing_since": None,
                }
            events[key]["blocks"].append(block)
            if logo and not events[key]["logo"]:
                events[key]["logo"] = logo
            continue
        i += 1
    return events


def rebuild_m3u_from_events(events: dict, filename: str) -> bool:
    """Write M3U from event state dict (preserves order of insertion)."""
    try:
        with open(filename, "w", encoding="utf-8") as f:
            f.write("#EXTM3U\n")
            f.write("# Playlist generated by Hotstar Extractor\n")
            f.write("# Playlist Created By @rtxcric\n")
            f.write(f"# Mode: FHD LIVE + HDNTL REFRESH (1 min) · grace {EVENT_GRACE_MINUTES}m\n")
            f.write(f"# Generated: {datetime.now(IST).strftime('%Y-%m-%d %I:%M:%S %p')}\n\n")
            for key, ev in events.items():
                for block in ev["blocks"]:
                    f.write(block if block.endswith("\n") else block + "\n")
        return True
    except Exception as e:
        print(f"{RED}M3U write error: {e}{RESET}")
        return False


def _fetch_short_hdntl_for_url(stream_url: str) -> str:
    """
    Prefer a shorter-lived hdntl/hdnea for (7M) variant.
    1) Fresh Set-Cookie from CDN
    2) Prefer token whose remaining TTL is closer to 7–12 min if multiple seen
    3) Fallback: same as normal embed cookie
    Note: Hotstar sports live often still signs ~30m; we always re-probe fresh.
    """
    raw = (stream_url or "").split("|")[0].strip()
    if not raw:
        return ""
    candidates = []

    # A) Set-Cookie (may be ~30m)
    try:
        tok = get_hdntl_token_4kads(raw, retries=2)
        if tok and "exp=" in tok:
            try:
                tok = _strip_hdntl_prefix(tok)
            except Exception:
                pass
            candidates.append(tok)
    except Exception:
        pass

    # B) Re-request URL: sometimes query hdnea is issued with different window
    try:
        headers = {
            "User-Agent": M3U_USER_AGENT,
            "Referer": M3U_REFERER,
            "Origin": M3U_ORIGIN,
            "Accept": "*/*",
        }
        req = request.Request(raw.split("?")[0] if "hdnea=" in raw else raw, headers=headers)
        # use URL with existing token so CDN responds
        req = request.Request(raw, headers=headers)
        with request.urlopen(req, timeout=12) as resp:
            sc = resp.headers.get("Set-Cookie") or ""
            try:
                all_sc = resp.headers.get_all("Set-Cookie") or []
                if all_sc:
                    sc = "\n".join(all_sc)
            except Exception:
                pass
            m = re.search(r"hdntl=([^;\s]+)", sc, flags=re.I)
            if m and "exp=" in m.group(1):
                candidates.append(m.group(1).strip())
            # Location redirect may carry short token
            loc = resp.headers.get("Location") or ""
            if "hdnea=" in loc or "hdntl=" in loc:
                t2 = extract_hdntl_from_url(loc) or ""
                if t2 and "exp=" in t2:
                    candidates.append(t2)
    except Exception:
        pass

    # C) token already on URL
    try:
        t3 = extract_hdntl_from_url(raw) or ""
        if t3 and "exp=" in t3:
            candidates.append(_strip_hdntl_prefix(t3))
    except Exception:
        pass

    if not candidates:
        return ""

    # Prefer remaining TTL in [5 min, 12 min]; else shortest remaining >= 5 min; else any
    scored = []
    now = int(time.time())
    for t in candidates:
        m = re.search(r"exp=(\d+)", t)
        if not m:
            continue
        left = int(m.group(1)) - now
        if left <= 60:
            continue
        # score: best if 5–12 min (300–720s)
        if 300 <= left <= 720:
            score = 0
        elif left < 300:
            score = 1
        else:
            score = 2 + min(left // 60, 100)  # longer = worse for 7M
        scored.append((score, left, t))

    if not scored:
        return candidates[0]

    scored.sort(key=lambda x: (x[0], x[1]))
    return scored[0][2]


def _classify_live_kind(title1: str, title2: str, url: str = "") -> str:
    """Return: sport | tv | show | other"""
    t1 = (title1 or "").upper()
    t2 = (title2 or "").upper()
    u = (url or "").lower()
    if "LIVE NEWS" in t1 or "/news/" in u:
        return "news"
    if "LIVE TV" in t1 or "/tv/" in u:
        return "tv"
    if "LIVE EPISODE" in t1:
        return "episode"
    if "LIVE SHOW" in t1 or "/shows/" in u:
        # episode watch page (not /live/watch) → LIVE EPISODE
        if _is_live_episode_slug(u) and "/live/watch" not in u:
            return "episode"
        return "show"
    return "sport"


def _group_title_for(title1: str, title2: str, url: str = "") -> str:
    t1 = (title1 or "").upper()
    t2 = (title2 or "").upper()
    u = (url or "").lower()
    kind = _classify_live_kind(title1, title2, url)
    if kind == "tv":
        return "LIVE TV: 24/7 by @rtxcric"
    if kind == "show":
        return "LIVE SHOW: 24/7 by @rtxcric"
    if kind == "episode":
        return "LIVE EPISODE by @rtxcric"
    # sports / other
    base = f"{title1}: {title2}" if title1 else (title2 or "LIVE")
    if "by @rtxcric" not in base.lower():
        base = f"{base} by @rtxcric"
    return base


def _clean_show_title(title2: str) -> str:
    """Strip junk from LIVE SHOW titles for clean channel labels.
    e.g. 'Bbs20: 24 Hrs Channel [Deferred]' → 'BBS20'
         'Bb: 24X7 Stream [Deferred]' → 'BB'
         'Bbs10   24X7 Stream [Deferred]' → 'BBS10'
    """
    t = (title2 or "").strip()
    if not t:
        return ""
    # Remove common deferred / 24x7 / channel noise (case-insensitive)
    junk_patterns = [
        r"\s*[:\-]?\s*24\s*x?7\s*stream\s*\[?deferred\]?\s*",
        r"\s*[:\-]?\s*24\s*hrs?\s*channel\s*\[?deferred\]?\s*",
        r"\s*\[deferred\]\s*",
        r"\s*\(deferred\)\s*",
        r"\s*24\s*x?7\s*",
        r"\s*24\s*hrs?\s*",
        r"\s*channel\s*",
        r"\s*stream\s*",
    ]
    cleaned = t
    for pat in junk_patterns:
        cleaned = re.sub(pat, " ", cleaned, flags=re.IGNORECASE)
    # Keep short show code / name; collapse spaces & trailing separators
    cleaned = re.sub(r"[\s:._-]+", " ", cleaned).strip(" :.-_")
    # Prefer first token if still long noise left
    if cleaned:
        # "BBS20 something" → "BBS20"
        parts = cleaned.split()
        if parts:
            # Prefer token that looks like show code (letters+digits)
            for p in parts:
                if re.match(r"^[A-Za-z]{1,6}\d{0,4}$", p):
                    return p.upper()
            return parts[0].upper()
    return t.upper()


def _format_hls_triple_blocks(
    lang: str,
    url: str,
    is_hdr: bool,
    drm_details: dict,
    title2: str,
    group_title: str,
    logo_url: str,
    raw_url: str = "",
    source_url: str = "",
) -> list:
    """
    One HLS stream → 3 M3U blocks:
      (30M)        — Cookie headers + hdnea in URL
      (30M STABLE) — NO cookie headers; hdnea in URL
      (7M)         — NO cookie headers; fresh cookie in URL
    """
    import hashlib
    raw = (url or "").split("|")[0].strip()
    token = extract_hdntl_from_url(raw) or ""
    if not token:
        m = re.search(r"(?:cookie|Cookie)=hdntl=([^&|]+)", url or "")
        if m:
            token = m.group(1).strip()
    try:
        token = _strip_hdntl_prefix(token)
    except Exception:
        pass

    # 7M = hot.py NORMAL FHD: use API stream query hdnea (short ~7–15 min)
    # NOT Set-Cookie (that is ~30 min, used for 30M / 30M STABLE)
    raw_src = (raw_url or raw or "").split("|")[0].strip()
    token_7m = ""
    try:
        token_7m = extract_hdntl_from_url(raw_src) or ""
        token_7m = _strip_hdntl_prefix(token_7m)
    except Exception:
        token_7m = ""
    if not token_7m:
        # last resort: fresh probe but prefer shorter remaining
        try:
            token_7m = _fetch_short_hdntl_for_url(raw_src or raw) or token
        except Exception:
            token_7m = token

    def _url_with_hdnea(base_url: str, tok: str) -> str:
        if not tok:
            return base_url.split("|")[0].strip()
        try:
            return append_hdntl_to_url_4kads(base_url.split("|")[0].strip(), tok)
        except Exception:
            u = base_url.split("|")[0].strip().split("?")[0]
            return f"{u}?a=ns&hdnea={tok}"

    url_30 = _url_with_hdnea(raw, token) if token else raw
    # 7M: base from API raw URL + short query token (hot.py NORMAL FHD style)
    base_7 = (raw_src or raw).split("?")[0]
    if token_7m:
        try:
            url_7 = append_hdntl_to_url_4kads(base_7, token_7m)
        except Exception:
            url_7 = f"{base_7}?a=ns&hdnea={token_7m}"
    else:
        url_7 = url_30

    # 7M: keep same CDN path as 30M (rewrite host), short token, WITH cookie headers so players work
    if token_7m:
        try:
            url_7 = append_hdntl_to_url_4kads((url_30 or raw).split("?")[0], token_7m)
        except Exception:
            url_7 = f"{(url_30 or raw).split('?')[0]}?a=ns&hdnea={token_7m}"
    elif token:
        # fallback: same URL as 30M (still playable)
        url_7 = url_30
        token_7m = token
    # FHD: only 30M + 30M STABLE (7M removed per request)
    variants = [
        ("30M", url_30, token, True),
        ("30M STABLE", url_30, token, False),
    ]
    # 4K HDR/SDR: only (30M STABLE) — no 7M (avoids real-token API refresh)
    if "4K" in str(lang).upper():
        raw4 = (url or raw or "").split("|")[0].strip()
        tok4 = extract_hdntl_from_url(raw4) or token or ""
        try:
            tok4 = _strip_hdntl_prefix(tok4) if tok4 else ""
        except Exception:
            pass
        tok_30 = ""
        try:
            tok_30 = get_hdntl_token_4kads(raw4, retries=4) or ""
            tok_30 = _strip_hdntl_prefix(tok_30) if tok_30 else ""
        except Exception:
            tok_30 = ""
        if not tok_30:
            tok_30 = tok4
        url_30_4k = raw4
        if tok_30:
            try:
                url_30_4k = append_hdntl_to_url_4kads(raw4, tok_30)
            except Exception:
                url_30_4k = raw4
        variants = [
            ("30M STABLE", url_30_4k, tok_30, False),
        ]

    blocks = []
    for vlabel, vurl, vtok, with_cookie_hdr in variants:
        # language from CDN path when available (biggboss-kan-2026 → KANNADA)
        _ln = _lang_from_stream_url(vurl, lang) or lang
        # strip trailing quality tags from lang for clean base name
        _ln_clean = re.sub(
            r"\s*(4K|FHD|HDR|SDR|30M|STABLE|7M|24H)\s*",
            " ",
            str(_ln),
            flags=re.I,
        ).strip()
        _ln_clean = re.sub(r"\s+", " ", _ln_clean).strip() or str(_ln)
        is_4k = "4K" in str(lang).upper() or "4K" in str(_ln).upper()
        if is_4k:
            if is_hdr or "HDR" in str(lang).upper():
                base_label = f"{_ln_clean} 4K HDR"
            elif "SDR" in str(lang).upper():
                base_label = f"{_ln_clean} 4K SDR"
            else:
                base_label = f"{_ln_clean} 4K"
        elif is_hdr:
            base_label = f"{_ln_clean} FHD HDR"
        else:
            base_label = f"{_ln_clean} FHD"
        # LIVE SHOW: clean short name + language so BBS10 Tamil/Telugu don't look identical
        if "LIVE SHOW" in (group_title or "") and (title2 or "").strip():
            _st = _clean_show_title(title2)
            # base_label already starts with language (TAMIL FHD / TELUGU FHD)
            channel_label = f"{_st}: {base_label} ({vlabel})" if _st else f"{base_label} ({vlabel})"
        else:
            channel_label = f"{base_label} ({vlabel})"
        tvg_id = str(int(hashlib.md5((vurl + vlabel).encode()).hexdigest(), 16) % 9999999999)
        _hs_cid = _content_id_from_url(source_url) if source_url else ""
        lines_out = []
        if logo_url:
            lines_out.append(
                f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title2}" '
                f'tvg-logo="{logo_url}" group-title="{group_title}", {channel_label} @rtxcric\n'
            )
        else:
            lines_out.append(
                f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title2}" '
                f'group-title="{group_title}", {channel_label} @rtxcric\n'
            )
        if _hs_cid:
            lines_out.append(f'#HS-CID:{_hs_cid}\n')
        if with_cookie_hdr and vtok:
            lines_out.append(
                f'#EXTHTTP:{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}",'
                f'"Cookie":"hdntl={vtok}"}}\n'
            )
            lines_out.append(f"#EXTVLCOPT:http-cookie=hdntl={vtok}\n")
        else:
            lines_out.append(
                f'#EXTHTTP:{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}"}}\n'
            )
        lines_out.append(f"#EXTVLCOPT:http-extra-headers=Origin: {M3U_ORIGIN}\n")
        lines_out.append(f"#EXTVLCOPT:http-referrer={M3U_REFERER}\n")
        lines_out.append(f"#EXTVLCOPT:http-user-agent={M3U_USER_AGENT}\n")
        lines_out.append(f"{vurl}\n")
        blocks.append("".join(lines_out))
    return blocks


def _format_single_block(
    lang: str,
    url: str,
    is_hdr: bool,
    drm_details: dict,
    title2: str,
    group_title: str,
    logo_url: str,
) -> str:
    """MPD / 24H / non-HLS single block."""
    import hashlib
    token_to_use = extract_hdntl_from_url(url) or ""
    if not token_to_use:
        _tok_m = re.search(r"(?:Cookie|cookie)=hdntl=([^&|]+)", url or "", flags=re.I)
        if _tok_m:
            token_to_use = unquote(_tok_m.group(1).strip())
    if not token_to_use:
        _tok_m2 = re.search(r"[?&]hdntl=([^&|]+)", url or "", flags=re.I)
        if _tok_m2:
            token_to_use = unquote(_tok_m2.group(1).strip())
    try:
        token_to_use = _strip_hdntl_prefix(token_to_use)
    except Exception:
        pass

    if "24H" in str(lang) or "(24H)" in str(lang):
        if not token_to_use:
            try:
                token_to_use = _strip_hdntl_prefix(get_24h_cookie_cached(force=False) or "")
            except Exception:
                token_to_use = ""
        # LIVE SHOW already has clean ?hdnea= URL from _format_entry_blocks.
        # Do NOT force pipe format again — only ensure we have a token for headers.
        # LIVE TV keeps pipe if it already has it.
        if token_to_use and "cookie=hdntl=" not in (url or "").lower() and "LIVE SHOW" not in (group_title or ""):
            url = append_hdntl_cookie_to_url(url, token_to_use)

    tvg_id = str(int(hashlib.md5(url.encode()).hexdigest(), 16) % 9999999999)
    # Clean token — never allow "tok|Cookie=hdntl=tok" leakage into headers
    if token_to_use:
        token_to_use = token_to_use.split("|")[0].split("&")[0].strip()
        token_to_use = re.sub(r"^(?:hdntl|hdnea)=", "", token_to_use, flags=re.I)
    # Language: prefer explicit path lang, else keep API lang label (do not invent ENGLISH)
    _lang = str(lang or "").strip()
    _from_url = _lang_from_stream_url(url, "")
    if _from_url:
        _base_tags = ""
        for _tag in ("24H", "30M STABLE", "30M", "7M"):
            if _tag in _lang:
                _base_tags = _tag
                break
        _lang = f"{_from_url} {_base_tags}".strip() if _base_tags else _from_url
    if "24H" in _lang and "(24H)" not in _lang:
        _lang = re.sub(r"\s*24H\s*", " ", _lang).strip()
        _lang = f"{_lang} (24H)".strip() if _lang else "(24H)"
    for _tag in ("30M STABLE", "30M", "7M"):
        if _tag in _lang and f"({_tag})" not in _lang:
            _lang = _lang.replace(_tag, "").strip()
            _lang = f"{_lang} ({_tag})".strip()
    gt = group_title or ""
    show_title = (title2 or "").strip()
    # Normalize tag placement like HLS: "ENGLISH FHD (30M)" / "ENGLISH FHD (24H)"
    _tag = ""
    for _t in ("30M STABLE", "30M", "7M", "24H"):
        if f"({_t})" in _lang or _t in _lang:
            _tag = _t
            _lang = re.sub(r"\s*\(?%s\)?" % re.escape(_t), " ", _lang).strip()
            _lang = re.sub(r"\s+", " ", _lang).strip()
            break
    _lu = str(lang or "").upper()
    _is_4k_lab = "4K" in _lu or "4K" in str(_lang).upper()
    # Detect HDR/SDR already in label so we never double them
    _has_hdr = bool(re.search(r"HDR", str(lang) + " " + str(_lang), flags=re.I))
    _has_sdr = bool(re.search(r"SDR", str(lang) + " " + str(_lang), flags=re.I))
    # Language name only — strip quality words
    _lang_clean = re.sub(
        r"(4K|FHD|HDR|SDR|30M|STABLE|7M|24H)",
        " ",
        _lang,
        flags=re.I,
    )
    _lang_clean = re.sub(r"\s+", " ", _lang_clean).strip(" -_")
    if _is_4k_lab:
        _dr = "HDR" if (is_hdr or _has_hdr) and not _has_sdr else "SDR"
        if _has_sdr and not is_hdr:
            _dr = "SDR"
        if is_hdr or (_has_hdr and not _has_sdr):
            _dr = "HDR"
        base_lab = f"{_lang_clean} 4K {_dr}".strip() if _lang_clean else f"4K {_dr}"
    else:
        if is_hdr:
            base_lab = f"{_lang_clean} FHD HDR".strip() if _lang_clean else "FHD HDR"
        else:
            base_lab = f"{_lang_clean} FHD".strip() if _lang_clean else "FHD"
    if _tag:
        base_lab = f"{base_lab} ({_tag})"
    if "LIVE SHOW" in gt and show_title:
        st = _clean_show_title(show_title)
        channel_label = f"{st}: {base_lab}" if st else base_lab
    else:
        channel_label = base_lab
    lines_out = []
    if logo_url:
        lines_out.append(
            f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title2}" '
            f'tvg-logo="{logo_url}" group-title="{group_title}", {channel_label} @rtxcric\n'
        )
    else:
        lines_out.append(
            f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title2}" '
            f'group-title="{group_title}", {channel_label} @rtxcric\n'
        )
    _drm_keys = list((drm_details or {}).get("keys") or [])
    if (drm_details or {}).get("is_drm") or ".mpd" in (url or "").lower():
        lines_out.append("#KODIPROP:inputstream.adaptive.manifest_type=mpd\n")
        if _drm_keys:
            lines_out.append("#KODIPROP:inputstream.adaptive.license_type=clearkey\n")
            lines_out.append(
                f"#KODIPROP:inputstream.adaptive.license_key={','.join(_drm_keys)}\n"
            )
    if not _drm_keys:
        _ck_m = re.search(r"(?:drmLicense|drm_license)=([0-9a-fA-F:,]+)", url or "")
        if _ck_m:
            _parsed = _ck_m.group(1).strip().rstrip("&|")
            lines_out.append("#KODIPROP:inputstream.adaptive.manifest_type=mpd\n")
            lines_out.append("#KODIPROP:inputstream.adaptive.license_type=clearkey\n")
            lines_out.append(
                f"#KODIPROP:inputstream.adaptive.license_key={_parsed}\n"
            )

    if "24H" in str(lang) or "cookie=hdntl=" in (url or "").lower():
        if token_to_use:
            lines_out.append(
                f'#EXTHTTP:{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}",'
                f'"Cookie":"hdntl={token_to_use}"}}\n'
            )
            lines_out.append(f"#EXTVLCOPT:http-cookie=hdntl={token_to_use}\n")
        else:
            lines_out.append(
                f'#EXTHTTP:{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}"}}\n'
            )
    else:
        _exthttp = f'{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}"'
        if token_to_use:
            _exthttp += f',"Cookie":"hdntl={token_to_use}"'
        _exthttp += "}"
        lines_out.append(f"#EXTHTTP:{_exthttp}\n")
        if token_to_use:
            lines_out.append(f"#EXTVLCOPT:http-cookie=hdntl={token_to_use}\n")
    lines_out.append(f"#EXTVLCOPT:http-extra-headers=Origin: {M3U_ORIGIN}\n")
    lines_out.append(f"#EXTVLCOPT:http-referrer={M3U_REFERER}\n")
    lines_out.append(f"#EXTVLCOPT:http-user-agent={M3U_USER_AGENT}\n")
    lines_out.append(f"{url}\n")
    return "".join(lines_out)


def _format_entry_blocks(
    lang: str,
    url: str,
    is_hdr: bool,
    drm_details: dict,
    title2: str,
    group_title: str,
    logo_url: str,
    raw_url: str = "",
    source_url: str = "",
) -> list:
    """
    Sports HLS + LIVE SHOW → 3 variants (30M / 30M STABLE / 7M);
    LIVE TV only → 24H (pipe cookie format);
    MPD sports → existing labels.
    LIVE SHOW does NOT use 24H cookie — same short-cookie streams as sports.
    """
    u = (url or "").split("|")[0].lower()
    is_hls = ".m3u8" in u
    is_mpd = ".mpd" in u
    gt = group_title or ""
    is_live_tv = "LIVE TV: 24/7" in gt
    # LIVE SHOW is treated like sports (triple 30M/STABLE/7M) — NOT 24H

    # LIVE TV only → single 24H stream
    if is_live_tv:
        if "30M" in str(lang) or "7M" in str(lang):
            return []
        base_lang = re.sub(r"\s*24H\s*", " ", str(lang or "")).strip() or "HINDI"
        try:
            tok24 = get_24h_cookie_cached(force=False) or ""
            tok24 = _strip_hdntl_prefix(tok24)
        except Exception:
            tok24 = ""
        base = (url or "").split("|")[0].split("?")[0]
        if tok24:
            url24 = append_hdntl_cookie_to_url(base, tok24)
        else:
            url24 = base
        return [
            _format_single_block(
                f"{base_lang} 24H", url24, is_hdr, drm_details or {}, title2, group_title, logo_url
            )
        ]

    blocks = []
    # LIVE SHOW + sports HLS → triple streams (no 24H)
    if is_hls and "24H" not in str(lang):
        blocks.extend(
            _format_hls_triple_blocks(
                lang, url, is_hdr, drm_details or {}, title2, group_title, logo_url,
                raw_url=raw_url or url, source_url=source_url or "",
            )
        )
    else:
        blocks.append(
            _format_single_block(
                lang, url, is_hdr, drm_details or {}, title2, group_title, logo_url
            )
        )
    return blocks


def append_event_blocks_to_m3u(
    filename: str,
    title1: str,
    title2: str,
    logo_url: str,
    entries: list,
    source_url: str = "",
) -> bool:
    """Append one event's channels to existing M3U file."""
    import hashlib
    try:
        existing = ""
        if os.path.isfile(filename):
            with open(filename, "r", encoding="utf-8") as f:
                existing = f.read()
        if not existing.strip():
            existing = (
                "#EXTM3U\n"
                "# Playlist generated by Hotstar Extractor\n"
                "# Playlist Created By @rtxcric\n"
                f"# Mode: FHD LIVE + HDNTL REFRESH (1 min) · grace {EVENT_GRACE_MINUTES}m\n"
                f"# Generated: {datetime.now(IST).strftime('%Y-%m-%d %I:%M:%S %p')}\n\n"
            )
        group_title = _group_title_for(title1, title2, "")
        chunks = []
        for entry in entries:
            raw_u = ""
            if len(entry) >= 5:
                lang, url, is_hdr, drm_details, raw_u = entry[:5]
            elif len(entry) >= 4:
                lang, url, is_hdr, drm_details = entry[:4]
            else:
                lang, url, is_hdr = entry[:3]
                drm_details = {}
            blocks = _format_entry_blocks(
                lang, url, is_hdr, drm_details or {}, title2, group_title, logo_url or "",
                raw_url=raw_u or "", source_url=source_url or "",
            )
            chunks.extend(blocks)
        with open(filename, "w", encoding="utf-8") as f:
            f.write(existing.rstrip() + "\n\n" + "".join(chunks))
        return True
    except Exception as e:
        print(f"{RED}Append M3U error: {e}{RESET}")
        return False


# =========================
# AUTO-UPDATE LOOP (new events once + h.py refresh every 1 min)
# =========================

def _event_keys_for_failed_urls(event_state: dict, failed_urls: list) -> set:
    """Map failed stream URLs back to event keys that own those blocks."""
    if not failed_urls:
        return set()
    failed_set = set()
    for u in failed_urls:
        base = u.split("?")[0].split("|")[0].strip().lower()
        failed_set.add(base)
        # also short path match
        failed_set.add(base.split("/")[-1] if "/" in base else base)
    keys = set()
    for key, meta in event_state.items():
        for block in meta.get("blocks") or []:
            for line in block.splitlines():
                s = line.strip()
                if not s.startswith("http"):
                    continue
                base = s.split("?")[0].split("|")[0].strip().lower()
                if base in failed_set or any(base.endswith(x) or x.endswith(base) for x in failed_set if len(x) > 20):
                    keys.add(key)
                    break
                # softer: host+path without query
                for fu in failed_urls:
                    fb = fu.split("?")[0].split("|")[0].strip().lower()
                    if fb and (fb in s.lower() or s.split("?")[0].lower() in fb):
                        keys.add(key)
                        break
    return keys


def _refetch_event_streams(key, meta, live_by_key, event_state, m3u_file):
    """Re-fetch FHD streams for one event using current token; replace blocks."""
    t1 = meta.get("title1") or ""
    t2 = meta.get("title2") or ""
    source_url = meta.get("source_url") or ""
    if key in live_by_key:
        ev = live_by_key[key]
        t1, t2, source_url = ev[0], ev[1], ev[2]
        meta["title1"], meta["title2"] = t1, t2
        meta["source_url"] = source_url
        if len(ev) > 3 and ev[3]:
            meta["logo"] = ev[3]
    if not source_url:
        print(f"  {YELLOW}⚠ No source URL for re-fetch: {t1}: {t2}{RESET}")
        return False
    print(f"  {BOLD_YELLOW}↻ Re-fetching FHD streams (token): {t1}: {t2}{RESET}")
    try:
        entries, logo = fetch_event_fhd_entries(t2, source_url, fast=False)
    except Exception as e:
        print(f"  {RED}✗ Re-fetch error: {e}{RESET}")
        return False
    # Keep existing 4K blocks — only cookie-refresh them (never re-discover URLs)
    old_4k_blocks = []
    for blk in (meta.get("blocks") or []):
        if "4K" in blk or "4kssai" in blk or "/out/v1/" in blk:
            # refresh hdnea on existing 4K lines
            lines_out = []
            for ln in blk.splitlines():
                s = ln.strip()
                if s.startswith("http"):
                    try:
                        lines_out.append(_embed_hdntl_in_url(s) or s)
                    except Exception:
                        lines_out.append(s)
                else:
                    lines_out.append(ln)
            old_4k_blocks.append("\n".join(lines_out))
    if old_4k_blocks:
        print(f"  {GREEN}✓ 4K kept + cookie refresh: {len(old_4k_blocks)} block(s){RESET}")
    if not entries and not old_4k_blocks:
        print(f"  {YELLOW}⚠ Re-fetch got 0 streams{RESET}")
        return False
    if logo:
        meta["logo"] = logo
    new_blocks = []
    group_title = _group_title_for(t1, t2, meta.get("source_url") or "")
    logo_url = meta.get("logo") or ""
    for entry in (entries or []):
        raw_u = ""
        if len(entry) >= 5:
            lang, url, is_hdr, drm_details, raw_u = entry[:5]
        elif len(entry) >= 4:
            lang, url, is_hdr, drm_details = entry[:4]
        else:
            lang, url, is_hdr = entry[:3]
            drm_details = {}
        blocks = _format_entry_blocks(
            lang, url, is_hdr, drm_details or {}, t2, group_title, logo_url,
            raw_url=raw_u or "",
        )
        new_blocks.extend(blocks)
    # append preserved 4K blocks after FHD
    new_blocks.extend(old_4k_blocks)
    meta["blocks"] = new_blocks
    meta["last_refetch"] = time.time()
    meta["refresh_fail_since"] = None
    if rebuild_m3u_from_events(event_state, m3u_file):
        print(f"  {GREEN}✓ Replaced streams for {t1}: {t2} ({len(new_blocks)} streams){RESET}")
        return True
    return False


def _rewrite_24h_blocks_in_m3u(content: str, new_token: str) -> tuple:
    """Replace hdntl/hdnea only inside 24H-labeled / ttl=86400 blocks."""
    if not new_token or not content:
        return content, 0
    lines = content.splitlines(keepends=True)
    # Find EXTINF blocks
    blocks = []  # (start, end)
    i = 0
    while i < len(lines):
        if lines[i].lstrip().startswith("#EXTINF"):
            start = i
            i += 1
            while i < len(lines) and not lines[i].lstrip().startswith("#EXTINF"):
                i += 1
            blocks.append((start, i))
            continue
        i += 1
    updated = 0
    for start, end in reversed(blocks):
        block = "".join(lines[start:end])
        if not is_24h_m3u_block(block):
            continue
        new_block = replace_token_in_block(block, new_token)
        # also ensure ttl=86400 stays
        if "ttl=86400" not in new_block and ".mpd" in new_block.lower():
            new_block = re.sub(
                r"(\?|&)(hdnea=)",
                lambda m: m.group(0) if "ttl=" in new_block else (m.group(1) + "ttl=86400&" + m.group(2) if m.group(1) == "?" else m.group(0)),
                new_block,
                count=1,
            )
        lines[start:end] = new_block.splitlines(keepends=True)
        updated += 1
    return "".join(lines), updated



# =============================================================================
# SONYLIV LIVE AUTO (embedded — no separate script)
# =============================================================================
import base64 as _sony_b64
import gzip as _sony_gzip
import http.cookiejar as _sony_cookiejar
import secrets as _sony_secrets
import zlib as _sony_zlib
import urllib.error as _sony_uerror
import urllib.request as _sony_ureq

_SONY_APIV2 = "https://apiv2.sonyliv.com"
_SONY_APIV3 = "https://apiv3.sonyliv.com"
_SONY_ORIGIN = "https://www.sonyliv.com"
_SONY_DAI = "https://sonydaimenew.akamaized.net/hls/live"
_SONY_UA_ANDROID = (
    "com.onemainstream.sonyliv.android/8.95 "
    "(Android 7.1.2; en_IN; AFTMM; Build/NS6281 )"
)
_SONY_UA_WEB = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
)
_SONY_CONTENT_ID_RE = re.compile(r"[-/](\d{7,12})(?:[/?#\-]|$)")
_SONY_TOKENS_FILE = "tokens.json"
_SONY_COOKIES_FILE = "sonycookies.txt"
_SONY_GRACE_MIN = 20
_SONY_COOKIE_REFRESH_SEC = 3 * 3600
_SONY_M3U_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:152.0) Gecko/20100101 Firefox/152.0"
_SONY_state = {}
_SONY_sess = None
_SONY_last_cookie_refresh = 0.0
_SONY_long_cache = {}

_SONY_NON_LIVE_RE = re.compile(
    r"(highlights?|interview|preview|recap|top\s*moments?|best\s*of|"
    r"press\s*conference|magazine|promo|trailer|shorts?|replay|"
    r"reviews?|shines?|delivers?|splendid|stunning\s*spell|"
    r"part\s*\d|episode|web\s*series)",
    re.I,
)
_SONY_SPORT_KW = {
    "cricket", "football", "soccer", "tennis", "hockey", "kabaddi",
    "wrestling", "wwe", "basketball", "golf", "sport", "ipl", "icc",
    "t20", "cup", "league", "vs", "ufc", "boxing",
}


def _sony_decode(data: bytes) -> str:
    for fn in (_sony_gzip.decompress, lambda d: _sony_zlib.decompress(d, -15)):
        try:
            return fn(data).decode("utf-8", errors="replace")
        except Exception:
            pass
    return data.decode("utf-8", errors="replace")


class _SonySession:
    def __init__(self):
        self.cj = _sony_cookiejar.MozillaCookieJar()
        self.opener = _sony_ureq.build_opener(_sony_ureq.HTTPCookieProcessor(self.cj))
        self.device_id = f"{_sony_secrets.token_hex(16)}-{int(time.time()*1000)}"
        self.session_id = f"{_sony_secrets.token_hex(16)}-{int(time.time()*1000)}"
        self.access_token = ""
        self.security_token = ""
        self.contact_id = ""

    def _headers(self, extra=None):
        h = {
            "User-Agent": _SONY_UA_ANDROID,
            "Accept": "application/json, text/plain, */*",
            "Accept-Encoding": "gzip, deflate, br",
            "Content-Type": "application/json",
            "Origin": _SONY_ORIGIN,
            "Referer": _SONY_ORIGIN + "/",
            "x-via-device": "true",
            "app_version": "6.12.35",
            "build_number": "10491",
            "device_id": self.device_id,
            "session_id": self.session_id,
        }
        if self.access_token:
            h["Authorization"] = self.access_token
        if self.security_token:
            h["security_token"] = self.security_token
        if extra:
            h.update(extra)
        return h

    def get(self, url, extra=None):
        try:
            req = _sony_ureq.Request(url, headers=self._headers(extra))
            with self.opener.open(req, timeout=25) as r:
                return json.loads(_sony_decode(r.read()))
        except Exception:
            return None

    def post(self, url, body, extra=None):
        try:
            data = json.dumps(body).encode()
            headers = self._headers(extra)
            headers["Content-Length"] = str(len(data))
            req = _sony_ureq.Request(url, data=data, headers=headers, method="POST")
            with self.opener.open(req, timeout=30) as r:
                return json.loads(_sony_decode(r.read()))
        except Exception:
            return None

    def load_cached_tokens(self) -> bool:
        for loc in (_SONY_TOKENS_FILE, os.path.join(os.path.expanduser("~"), _SONY_TOKENS_FILE)):
            if not os.path.exists(loc):
                continue
            try:
                with open(loc, encoding="utf-8") as f:
                    t = json.load(f)
                self.access_token = t.get("token", "")
                self.session_id = t.get("session_id", self.session_id)
                self.security_token = t.get("security_token", "")
                self.device_id = t.get("device_id", self.device_id)
                self.contact_id = t.get("contact_id", "")
                return bool(self.access_token)
            except Exception:
                pass
        return False

    def load_cookies(self, path=_SONY_COOKIES_FILE) -> int:
        for loc in (
            path,
            os.path.join(os.path.expanduser("~"), path),
            f"/data/data/com.termux/files/home/{path}",
        ):
            if not os.path.exists(loc):
                continue
            try:
                self.cj.load(loc, ignore_discard=True, ignore_expires=True)
                for c in self.cj:
                    if c.name.lower() in (
                        "at", "authorization", "access_token", "accesstoken",
                        "sl_at", "sl_access_token",
                    ):
                        self.access_token = c.value
                return len(list(self.cj))
            except Exception:
                pass
        return 0


def _sony_fetch_security_token(sess: _SonySession) -> bool:
    url = f"{_SONY_APIV2}/AGL/1.5/A/ENG/FIRE_TV/IN/GETTOKEN"
    try:
        req = _sony_ureq.Request(url, headers={"User-Agent": "okhttp/3.14.9"})
        with _sony_ureq.urlopen(req, timeout=15) as r:
            data = json.loads(_sony_decode(r.read()))
        token = data.get("resultObj") or ""
        if token and isinstance(token, str):
            sess.security_token = token
            return True
    except Exception:
        pass
    return False


def _sony_authenticate(sess: _SonySession) -> bool:
    url = f"{_SONY_APIV2}/AGL/2.9/A/ENG/WEB/IN/BR/GETPROFILE?channelPartnerID=MSMIND"
    data = sess.get(url)
    if not data or data.get("resultCode") != "OK":
        return False
    ro = data.get("resultObj") or {}
    token = ro.get("accessToken") or sess.access_token
    if not token:
        return False
    sess.access_token = token
    try:
        parts = token.split(".")
        payload = parts[1] + "=" * ((4 - len(parts[1]) % 4) % 4)
        pl = json.loads(_sony_b64.urlsafe_b64decode(payload))
        sess.contact_id = str(pl.get("contactID") or "")
    except Exception:
        pass
    return True


def _sony_get_session() -> _SonySession:
    global _SONY_sess
    if _SONY_sess is not None:
        return _SONY_sess
    sess = _SonySession()
    authed = False
    if sess.load_cached_tokens():
        _sony_fetch_security_token(sess)
        authed = _sony_authenticate(sess)
        if not authed:
            sess.access_token = ""
    if not authed:
        if sess.load_cookies():
            _sony_fetch_security_token(sess)
            _sony_authenticate(sess)
        else:
            _sony_fetch_security_token(sess)
    _SONY_sess = sess
    return sess


def _sony_is_real_live(item: dict) -> bool:
    title = (item.get("title") or "").strip()
    if not title or _SONY_NON_LIVE_RE.search(title):
        return False
    if not item.get("live"):
        return False
    if item.get("is_show"):
        return False
    ctype = str(item.get("ctype") or "").upper()
    if ctype in ("SHOW", "SERIES", "TVSHOW", "EPISODE", "CLIP", "VOD", "HIGHLIGHT"):
        return False
    tl = title.lower()
    has_vs = (" vs " in tl) or (" v " in tl) or (" vs. " in tl)
    if ctype in ("LIVE_SPORT", "LIVE", "EVENT", "MATCH") or has_vs:
        return True
    genres = " ".join(item.get("genres") or []).lower()
    if any(k in genres or k in tl for k in _SONY_SPORT_KW) and has_vs:
        return True
    return False


def _sony_list_live(sess: _SonySession) -> list:
    items = []

    def _push(cid, title, live=False, ctype="", genres=None, is_show=False, league=""):
        if not cid or not title:
            return
        if any(x["id"] == str(cid) for x in items):
            return
        items.append({
            "id": str(cid), "title": str(title).strip(),
            "league": str(league or "").strip(), "live": bool(live),
            "ctype": ctype or "", "genres": genres or [], "is_show": bool(is_show),
        })

    def _walk(containers, live_only=True):
        for c in containers or []:
            if not isinstance(c, dict):
                continue
            if c.get("containers"):
                _walk(c.get("containers"), live_only)
            m = c.get("metadata") or {}
            cid = str(c.get("id") or m.get("contentId") or "")
            league = (m.get("title") or m.get("seriesTitle") or m.get("showTitle") or "").strip()
            match = (m.get("episodeTitle") or "").strip()
            if not match:
                match, league = league, ""
            title = match or league
            if not title:
                continue
            is_live = bool(m.get("isLive") or m.get("isOnAir") or m.get("isLiveEvent"))
            if live_only and not is_live:
                continue
            ctype = m.get("contentSubtype") or m.get("objectSubtype") or ""
            is_show = str(ctype).upper() in ("SHOW", "SERIES", "TVSHOW", "TVSERIES", "EPISODE")
            _push(cid, title, is_live, ctype, m.get("genres") or [], is_show, league)

    for coll in ("3937924064", "9014016", "9015093"):
        d = sess.get(
            f"{_SONY_APIV3}/AGL/4.9/R/ENG/WEB/IN/MH/TRAY/EXTCOLLECTION/{coll}"
            f"?layout=portrait_layout&SSR=false&from=0&to=30&kids_safe=false"
        )
        if d and d.get("resultCode") == "OK":
            _walk((d.get("resultObj") or {}).get("containers") or [], True)
        if len(items) >= 5:
            break
    if len(items) < 2:
        d = sess.get(f"{_SONY_APIV2}/AGL/1.4/R/ENG/WEB/IN/MH/LIVE/LIVELISTING")
        if d and d.get("resultCode") == "OK":
            _walk((d.get("resultObj") or {}).get("containers") or [], True)

    live = [it for it in items if _sony_is_real_live(it)]
    if not live:
        live = [it for it in items if it.get("live") and not _SONY_NON_LIVE_RE.search(it.get("title") or "")]
    return live[:20]


def _sony_fetch_detail(sess, content_id: str) -> dict:
    urls = [
        f"{_SONY_APIV3}/AGL/4.8/A/ENG/WEB/IN/MH/DETAIL-V2/{content_id}?kids_safe=false&from=0&to=9",
        f"{_SONY_APIV3}/AGL/4.8/R/ENG/WEB/IN/MH/DETAIL-V2/{content_id}?kids_safe=false&from=0&to=9",
        f"{_SONY_APIV2}/AGL/2.6/SR/ENG/WEB/IN/MH/DETAIL-V2/{content_id}",
    ]
    for url in urls:
        data = sess.get(url)
        if not data or data.get("resultCode") != "OK":
            continue
        containers = ((data.get("resultObj") or {}).get("containers") or [])
        if not containers:
            continue
        c = containers[0]
        meta = c.get("metadata") or {}
        emf = meta.get("emfAttributes") or {}
        logo = ""
        for key in ("landscape_thumb", "landscape", "masthead_logo_rectangular", "masthead_logo", "thumbnail", "poster"):
            v = emf.get(key) or meta.get(key) or ""
            if isinstance(v, str) and v.startswith("http"):
                logo = v
                break
            if isinstance(v, dict):
                u = v.get("url") or v.get("src") or ""
                if u.startswith("http"):
                    logo = u
                    break
        title = (meta.get("episodeTitle") or meta.get("title") or "").strip()
        league = (meta.get("title") if meta.get("episodeTitle") else "") or meta.get("seriesTitle") or ""
        return {"content_id": content_id, "title": title, "league": (league or "").strip(), "logo": logo}
    return {"content_id": content_id, "title": "", "league": "", "logo": ""}


def _sony_fetch_video_url(sess, content_id: str) -> dict:
    """Exact same endpoint order as sony.py (HAR-verified)."""
    contact_qs = f"?contactId={sess.contact_id}" if sess.contact_id else ""
    ppid = sess.device_id
    body_base = {
        "actionType": "play", "browser": "Chrome", "deviceId": sess.device_id,
        "os": "Android", "platform": "web", "hasLAURLEnabled": True,
        "adsParams": {"Idtype": "uuid", "Is_lat": "0", "ppid": ppid},
    }
    extra_web = {"app_version": "3.6.79", "advertiserid": sess.device_id}
    extra_tv = {
        "td_client_hints": json.dumps({
            "os_name": "Android", "os_version": "10",
            "device_make": "Amazon", "device_model": "AFTMM",
            "display_res": "1080", "viewport_res": "1080",
            "supp_codec": "H264,AAC,EAC3,AC3",
            "audio_decoder": "EAC3,AAC,AC3", "hdr_decoder": "SDR",
        }),
        "advertiserid": sess.device_id,
    }
    endpoints = []
    if sess.access_token:
        endpoints.extend([
            (f"{_SONY_APIV2}/AGL/5.0/A/ENG/WEB/IN/MH/CONTENT/VIDEOURL/VOD/{content_id}{contact_qs}", extra_web, body_base),
            (f"{_SONY_APIV2}/AGL/5.0/R/ENG/WEB/IN/MH/CONTENT/VIDEOURL/VOD/{content_id}{contact_qs}", extra_web, body_base),
            (f"{_SONY_APIV2}/AGL/3.3/SR/ENG/FIRE_TV/IN/TN/CONTENT/VIDEOURL/VOD/{content_id}{contact_qs}", extra_tv, body_base),
            (f"{_SONY_APIV2}/AGL/3.3/SR/ENG/SONY_ANDROID_TV/IN/TN/CONTENT/VIDEOURL/VOD/{content_id}{contact_qs}", extra_tv, body_base),
            (f"{_SONY_APIV2}/AGL/5.0/A/ENG/WEB/IN/MH/CONTENT/VIDEOURL/LIVE/{content_id}{contact_qs}", extra_web, body_base),
            (f"{_SONY_APIV2}/AGL/3.3/SR/ENG/FIRE_TV/IN/TN/CONTENT/VIDEOURL/LIVE/{content_id}{contact_qs}", extra_tv, body_base),
        ])
    endpoints.extend([
        (f"{_SONY_APIV2}/AGL/5.0/A/ENG/WEB/IN/MH/CONTENT/VIDEOURL/VOD/{content_id}/freepreview", extra_web, body_base),
        (f"{_SONY_APIV2}/AGL/5.0/R/ENG/WEB/IN/MH/CONTENT/VIDEOURL/VOD/{content_id}/freepreview", extra_web, body_base),
        (f"{_SONY_APIV2}/AGL/5.0/A/ENG/WEB/IN/MH/CONTENT/VIDEOURL/LIVE/{content_id}/freepreview", extra_web, body_base),
        (f"{_SONY_APIV2}/AGL/5.0/A/ENG/WEB/IN/MH/CONTENT/VIDEOURL/VOD/{content_id}{contact_qs}", extra_web, body_base),
        (f"{_SONY_APIV2}/AGL/3.3/SR/ENG/FIRE_TV/IN/TN/CONTENT/VIDEOURL/VOD/{content_id}{contact_qs}", extra_tv, body_base),
    ])
    last_msg = ""
    for url, extra, body in endpoints:
        resp = sess.post(url, body, extra)
        if not resp or resp.get("resultCode") != "OK":
            continue
        ro = resp.get("resultObj") or {}
        if not (ro.get("videoURL") or ro.get("multiLanguageVideoURL")):
            continue
        # multi-lang expansion like sony.py
        langs = ro.get("audioLanguages") or ro.get("languages") or []
        primary = ro.get("videoURL") or ""
        multi = list(ro.get("multiLanguageVideoURL") or [])
        if isinstance(multi, dict):
            multi = [{"videoURL": v, "audioLanguageName": k} for k, v in multi.items()]
        have = set()
        for item in multi:
            if isinstance(item, dict):
                code = (item.get("audioLanguageName") or "").upper().strip()
                if code:
                    have.add(code)
        primary_code = ""
        m = re.search(r"/(ENG|HIN|TAM|TEL|KAN|MAL|BEN|MAR|GUJ|PUN|PAN|ORI|URD)/", primary or "", re.I)
        if m:
            primary_code = m.group(1).upper()
            have.add(primary_code)
        if langs and primary:
            for item in langs:
                if not isinstance(item, dict):
                    continue
                code = (item.get("audioLanguageName") or "").upper().strip()
                label = (item.get("audioLanguageLabel") or code).strip()
                if not code or code in have:
                    continue
                if code == primary_code:
                    multi.append({"videoURL": primary, "audioLanguageName": code, "audioLanguageLabel": label})
                    have.add(code)
                    continue
                sep = "&" if "?" in url else "?"
                lang_url = f"{url}{sep}audio={code}"
                resp2 = sess.post(lang_url, body, extra)
                if resp2 and resp2.get("resultCode") == "OK":
                    u2 = (resp2.get("resultObj") or {}).get("videoURL") or ""
                    if u2:
                        multi.append({"videoURL": u2, "audioLanguageName": code, "audioLanguageLabel": label})
                        have.add(code)
                        continue
                if primary_code:
                    u2 = re.sub(r"/" + re.escape(primary_code) + r"(?=/)", "/" + code, primary, count=1, flags=re.I)
                    if u2 != primary:
                        multi.append({"videoURL": u2, "audioLanguageName": code, "audioLanguageLabel": label})
                        have.add(code)
            if multi:
                ro["multiLanguageVideoURL"] = multi
        return ro
    return {}


def _sony_dai_from_ame(master_url: str) -> str:
    """AME → DAI master rewrite (sony.py)."""
    m = re.search(
        r"sonymtmnew\.akamaized\.net/v1/master/[^/]+/[^/]+/(\d+)/([^/]+)/([A-Z]{2,4})/([^?]+\.m3u8)",
        master_url or "", re.I,
    )
    if not m:
        return ""
    ch_id, event, lang, _prof = m.group(1), m.group(2), m.group(3).upper(), m.group(4)
    hdnea_m = re.search(r"[?&]hdnea=([^&]+)", master_url or "")
    if not hdnea_m:
        return ""
    return f"{_SONY_DAI}/{ch_id}/{event}/{lang}/master.m3u8?hdnea={hdnea_m.group(1)}"


def _sony_lang_label(code: str) -> str:
    names = {
        "ENG": "ENGLISH", "HIN": "HINDI", "TAM": "TAMIL", "TEL": "TELUGU",
        "KAN": "KANNADA", "MAL": "MALAYALAM", "BEN": "BENGALI", "MAR": "MARATHI",
        "GUJ": "GUJARATI", "PUN": "PUNJABI", "PAN": "PUNJABI", "ORI": "ODIA",
    }
    return names.get((code or "").upper(), (code or "STREAM").upper())


def _sony_extract_entries(vr: dict) -> list:
    """Same multi-lang extraction as sony.py _extract_all_stream_entries (simplified return)."""
    entries = []
    seen = set()

    def add(u, label="", code=""):
        if not u or not str(u).startswith("http"):
            return
        code = (code or "").upper()
        if not code:
            m = re.search(r"/(ENG|HIN|TAM|TEL|KAN|MAL|BEN|MAR|GUJ|PUN|PAN|ORI|URD)/", u, re.I)
            code = m.group(1).upper() if m else "HIN"
        if code in seen:
            return
        seen.add(code)
        entries.append({"url": u, "lang": label or _sony_lang_label(code), "lang_code": code})

    multi = vr.get("multiLanguageVideoURL")
    if isinstance(multi, list):
        for item in multi:
            if isinstance(item, dict):
                u = item.get("videoURL") or item.get("url") or ""
                code = item.get("audioLanguageName") or item.get("language") or ""
                label = item.get("audioLanguageLabel") or ""
                add(u, label or _sony_lang_label(str(code)), str(code))
            elif isinstance(item, str):
                add(item)
    elif isinstance(multi, dict):
        for code, u in multi.items():
            if isinstance(u, str):
                add(u, _sony_lang_label(str(code)), str(code))
            elif isinstance(u, dict):
                add(u.get("videoURL") or u.get("url") or "", _sony_lang_label(str(code)), str(code))

    primary = vr.get("videoURL") or ""
    if isinstance(primary, dict):
        primary = primary.get("videoURL") or primary.get("url") or ""
    if primary:
        add(primary)
    return entries


def _sony_fetch_long_hdnea(lang_code: str = "") -> str:
    global _SONY_long_cache
    key = (lang_code or "").upper() or "_"
    now = time.time()
    cached = _SONY_long_cache.get(key)
    if cached and now - cached[1] < 1800:
        return cached[0]
    for k, (tok, ts) in list(_SONY_long_cache.items()):
        if now - ts < 1800 and tok:
            return tok
    sources = [
        "https://raw.githubusercontent.com/drmlive/sliv-live-events/main/sonyliv.json",
        "https://raw.githubusercontent.com/drmlive/sliv-live-events/main/sonyliv.m3u",
    ]
    found = ""
    for src in sources:
        try:
            req = _sony_ureq.Request(src, headers={"User-Agent": _SONY_UA_WEB})
            with _sony_ureq.urlopen(req, timeout=12) as r:
                raw = r.read().decode("utf-8", errors="replace")
            if src.endswith(".json"):
                data = json.loads(raw)
                for m in (data.get("matches") or []):
                    if m.get("isLive") is False:
                        continue
                    u = m.get("dai_url") or m.get("video_url") or m.get("pub_url") or ""
                    if "hdnea=" not in u:
                        continue
                    hm = re.search(r"(hdnea=[^&\s\"']+)", u)
                    if hm:
                        found = hm.group(1)
                        if key == "_" or f"/{key}/" in u.upper():
                            break
            else:
                for line in raw.splitlines():
                    if "sonydaimenew" in line and "hdnea=" in line:
                        hm = re.search(r"(hdnea=[^&\s\"']+)", line)
                        if not hm:
                            continue
                        if key != "_" and f"/{key}/" not in line.upper():
                            if not found:
                                found = hm.group(1)
                            continue
                        found = hm.group(1)
                        break
            if found:
                break
        except Exception:
            continue
    if found:
        _SONY_long_cache[key] = (found, now)
        _SONY_long_cache["_"] = (found, now)
    return found


def _sony_apply_long_hdnea(url: str, lang_code: str = "") -> str:
    if not url:
        return url
    final = url
    if "sonydaimenew" not in final and ".mpd" not in final.lower():
        dai = _sony_dai_from_ame(final)
        if dai:
            final = dai
    if "sonydaimenew" not in final:
        return final
    base = final.split("?")[0]
    base = re.sub(r"std_lrl[-\d]+", "master", base)
    base = re.sub(r"std_mdh[-\d]+", "master", base)
    tok = _sony_fetch_long_hdnea(lang_code)
    if tok:
        return f"{base}?{tok}"
    if "hdnea=" in final:
        hm = re.search(r"(hdnea=[^&\s]+)", final)
        if hm:
            return f"{base}?{hm.group(1)}"
    return base


def _sony_format_blocks(title, league, logo, streams, content_id) -> list:
    import hashlib
    if league:
        group = f"SONY LIVE: {league} by @rtxcric"
    else:
        group = f"SONY LIVE: {title} by @rtxcric"
    blocks = []
    for s in streams:
        lang = s.get("lang") or "HINDI"
        url = s.get("url") or ""
        if not url:
            continue
        label = f"{lang} FHD"
        tvg_id = str(int(hashlib.md5((url + content_id).encode()).hexdigest(), 16) % 9999999999)
        lines = []
        if logo:
            lines.append(
                f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title}" '
                f'tvg-logo="{logo}" group-title="{group}", {label} @rtxcric\n'
            )
        else:
            lines.append(
                f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title}" '
                f'group-title="{group}", {label} @rtxcric\n'
            )
        lines.append(f"#HS-SONY-ID:{content_id}\n")
        lines.append(f'#EXTHTTP:{{"Origin":"{_SONY_ORIGIN}","Referer":"{_SONY_ORIGIN}/"}}\n')
        lines.append(f"#EXTVLCOPT:http-extra-headers=Origin: {_SONY_ORIGIN}\n")
        lines.append(f"#EXTVLCOPT:http-referrer={_SONY_ORIGIN}/\n")
        lines.append(f"#EXTVLCOPT:http-user-agent={_SONY_M3U_UA}\n")
        lines.append(f"{url}\n")
        blocks.append("".join(lines))
    return blocks


def _sony_fetch_event_streams(sess, content_id: str):
    meta = _sony_fetch_detail(sess, content_id) or {}
    meta["content_id"] = content_id
    vr = _sony_fetch_video_url(sess, content_id)
    if not vr:
        return [], meta
    entries = _sony_extract_entries(vr)
    streams = []
    for e in entries:
        u = _sony_apply_long_hdnea(e["url"], e.get("lang_code", ""))
        streams.append({"lang": e["lang"], "url": u, "lang_code": e.get("lang_code", "")})
    return streams, meta


def _sony_parse_ids_from_m3u(content: str) -> dict:
    out = {}
    lines = content.splitlines(keepends=True)
    i = 0
    while i < len(lines):
        if lines[i].lstrip().startswith("#EXTINF") and "SONY LIVE" in lines[i]:
            start = i
            i += 1
            while i < len(lines) and not lines[i].lstrip().startswith("#EXTINF"):
                i += 1
            block = "".join(lines[start:i])
            m = re.search(r"#HS-SONY-ID:(\d+)", block)
            cid = m.group(1) if m else ""
            if cid:
                out.setdefault(cid, []).append(block)
            continue
        i += 1
    return out


def _sony_rebuild_without_ids(content: str, remove_ids: set) -> str:
    lines = content.splitlines(keepends=True)
    out = []
    i = 0
    while i < len(lines):
        if lines[i].lstrip().startswith("#EXTINF"):
            start = i
            i += 1
            while i < len(lines) and not lines[i].lstrip().startswith("#EXTINF"):
                i += 1
            block = "".join(lines[start:i])
            if "SONY LIVE" in block:
                m = re.search(r"#HS-SONY-ID:(\d+)", block)
                cid = m.group(1) if m else ""
                if cid and cid in remove_ids:
                    continue
            out.append(block)
            continue
        out.append(lines[i])
        i += 1
    return "".join(out)


def _sony_refresh_hdnea_in_m3u(content: str):
    lines = content.splitlines(keepends=True)
    blocks = []
    i = 0
    while i < len(lines):
        if lines[i].lstrip().startswith("#EXTINF") and "SONY LIVE" in lines[i]:
            start = i
            i += 1
            while i < len(lines) and not lines[i].lstrip().startswith("#EXTINF"):
                i += 1
            blocks.append((start, i))
            continue
        i += 1
    updated = 0
    for start, end in reversed(blocks):
        block = "".join(lines[start:end])
        new_lines = []
        changed = False
        for ln in block.splitlines(keepends=True):
            s = ln.strip()
            if s.startswith("http") and "sonydaimenew" in s:
                code = ""
                m = re.search(r"/(ENG|HIN|TAM|TEL|KAN|MAL|BEN|MAR|GUJ|PUN|PAN)/", s, re.I)
                if m:
                    code = m.group(1).upper()
                new_u = _sony_apply_long_hdnea(s, code)
                if new_u and new_u != s:
                    ends = "\r\n" if ln.endswith("\r\n") else "\n"
                    new_lines.append(new_u + ends)
                    changed = True
                    continue
            new_lines.append(ln)
        if changed:
            lines[start:end] = new_lines
            updated += 1
    return "".join(lines), updated


def _sony_append_blocks(filename: str, blocks: list) -> bool:
    try:
        existing = ""
        if os.path.isfile(filename):
            with open(filename, "r", encoding="utf-8") as f:
                existing = f.read()
        if not existing.strip():
            existing = (
                "#EXTM3U\n# Playlist generated by Hotstar+Sony Extractor\n"
                f"# Generated: {datetime.now(IST).strftime('%Y-%m-%d %I:%M:%S %p')}\n\n"
            )
        with open(filename, "w", encoding="utf-8") as f:
            f.write(existing.rstrip() + "\n\n" + "".join(blocks))
        return True
    except Exception as e:
        print(f"  {YELLOW}Sony M3U append error: {e}{RESET}")
        return False


def sony_auto_cycle(m3u_file: str) -> bool:
    """Sony live: detect / add / 3h cookie refresh / 20m grace remove."""
    global _SONY_state, _SONY_last_cookie_refresh, _SONY_long_cache
    changed = False
    try:
        sess = _sony_get_session()
    except Exception as e:
        print(f"  {YELLOW}⚠ Sony session: {e}{RESET}")
        return False

    print(f"  {DARK_MAGENTA}→ Sony live check...{RESET}", end="", flush=True)
    try:
        live = _sony_list_live(sess)
    except Exception as e:
        print(f"\r  {YELLOW}⚠ Sony list error: {e}{RESET}")
        return False
    print(f"\r  {GREEN}✓ Sony: {len(live)} live event(s){RESET}            ")

    live_ids = {it["id"] for it in live}
    live_by_id = {it["id"]: it for it in live}
    now = time.time()

    if os.path.isfile(m3u_file) and not _SONY_state:
        try:
            with open(m3u_file, "r", encoding="utf-8") as f:
                existing_map = _sony_parse_ids_from_m3u(f.read())
            for cid, blocks in existing_map.items():
                _SONY_state[cid] = {
                    "title": "", "league": "", "blocks": blocks,
                    "last_seen": now, "missing_since": None,
                }
        except Exception:
            pass

    for cid in live_ids:
        if cid in _SONY_state:
            _SONY_state[cid]["last_seen"] = now
            _SONY_state[cid]["missing_since"] = None

    for cid in [c for c in live_ids if c not in _SONY_state]:
        it = live_by_id[cid]
        print(f"  {BOLD_YELLOW}★ Sony NEW: {it.get('league','')} {it.get('title','')}{RESET}")
        try:
            streams, meta = _sony_fetch_event_streams(sess, cid)
        except Exception as e:
            print(f"  {YELLOW}⚠ Sony fetch {cid}: {e}{RESET}")
            continue
        if not streams:
            print(f"  {YELLOW}⚠ Sony {cid}: no streams{RESET}")
            continue
        title = meta.get("title") or it.get("title") or cid
        league = meta.get("league") or it.get("league") or "SonyLiv"
        logo = meta.get("logo") or ""
        blocks = _sony_format_blocks(title, league, logo, streams, cid)
        if _sony_append_blocks(m3u_file, blocks):
            _SONY_state[cid] = {
                "title": title, "league": league, "logo": logo,
                "blocks": blocks, "last_seen": now, "missing_since": None,
            }
            changed = True
            langs = ", ".join(s["lang"] for s in streams)
            print(f"  {GREEN}✓ Sony ADDED: {title} → {len(streams)} stream(s) [{langs}]{RESET}")

    # 3h cookie refresh
    if now - _SONY_last_cookie_refresh >= _SONY_COOKIE_REFRESH_SEC or _SONY_last_cookie_refresh == 0:
        if os.path.isfile(m3u_file):
            try:
                with open(m3u_file, "r", encoding="utf-8") as f:
                    content = f.read()
                if "SONY LIVE" in content:
                    _SONY_long_cache.clear()
                    new_c, n = _sony_refresh_hdnea_in_m3u(content)
                    if n:
                        with open(m3u_file, "w", encoding="utf-8") as f:
                            f.write(new_c)
                        changed = True
                        print(f"  {GREEN}✓ Sony cookie refresh: {n} stream(s){RESET}")
                    else:
                        print(f"  {GRAY}· Sony cookies still valid{RESET}")
                _SONY_last_cookie_refresh = now
            except Exception as e:
                print(f"  {YELLOW}⚠ Sony cookie refresh: {e}{RESET}")
        else:
            _SONY_last_cookie_refresh = now

    to_remove = []
    for cid, meta in list(_SONY_state.items()):
        if cid in live_ids:
            continue
        if meta.get("missing_since") is None:
            meta["missing_since"] = now
            print(f"  {YELLOW}⏳ Sony missing (grace): {meta.get('title') or cid}{RESET}")
        else:
            gone = (now - meta["missing_since"]) / 60.0
            if gone >= _SONY_GRACE_MIN:
                to_remove.append(cid)
                print(f"  {RED}🗑 Sony remove ({gone:.0f}m): {meta.get('title') or cid}{RESET}")
            else:
                print(f"  {GRAY}· Sony still missing {meta.get('title') or cid} "
                      f"({_SONY_GRACE_MIN - gone:.0f}m left){RESET}")

    if to_remove and os.path.isfile(m3u_file):
        try:
            with open(m3u_file, "r", encoding="utf-8") as f:
                content = f.read()
            new_c = _sony_rebuild_without_ids(content, set(to_remove))
            with open(m3u_file, "w", encoding="utf-8") as f:
                f.write(new_c)
            for cid in to_remove:
                _SONY_state.pop(cid, None)
            changed = True
        except Exception as e:
            print(f"  {YELLOW}⚠ Sony remove write: {e}{RESET}")

    return changed

# =============================================================================
# END SONYLIV EMBED
# =============================================================================


def auto_update_mode():
    global _ACTIVE_TOKEN_OVERRIDE

    print(f"\n{BOLD_CYAN}╔══════════════════════════════════════════╗{RESET}")
    print(f"{BOLD_CYAN}║  🔴  FHD LIVE + HDNTL AUTO-REFRESH      ║{RESET}")
    print(f"{BOLD_CYAN}║  New events once · cookie refresh 1min  ║{RESET}")
    print(f"{BOLD_CYAN}║  Remove gone events after {EVENT_GRACE_MINUTES} min grace    ║{RESET}")
    print(f"{BOLD_CYAN}╚══════════════════════════════════════════╝{RESET}\n")

    # ── 1. Cloudflare config ──────────────────────────────────────────────────
    cf_config = load_cf_config_fhd()
    cf_worker_url = cf_config["worker_url"]
    cf_api_token  = cf_config["api_token"]
    print(f"{GREEN}✓ Cloudflare Worker: {CYAN}{cf_worker_url}{RESET}")
    print(f"{GRAY}  (config baked into script; optional {LIVE_CF_CONFIG} can override){RESET}")

    # ── 2. Proxy (needed for token/API calls when fetching NEW streams) ───────
    ()

    # ── 3. Tokens — ONLY for discovering live list + fetching NEW streams ─────
    print(f"{BOLD_YELLOW}Loading FHD tokens from {FHD_TOKEN_DIR}/{RESET}")
    all_tokens = load_fhd_tokens()
    if not all_tokens:
        print(f"{RED}✗ No tokens found in {FHD_TOKEN_DIR}/{RESET}")
        print(f"{YELLOW}  Falling back to token.txt{RESET}")
        fallback = load_user_token()
        if not fallback:
            print(f"{RED}✗ No token.txt either. Cannot fetch new events.{RESET}")
            return
        all_tokens = [(0, fallback, TOKEN_FILE)]
    else:
        print(f"{GREEN}✓ Found {len(all_tokens)} token files{RESET}")

    valid_tokens = fast_check_all_tokens(all_tokens)
    if not valid_tokens:
        print(f"{RED}✗ ALL tokens expired! Add fresh tokens and restart.{RESET}")
        return

    expired_set = set()
    skip_set = set()
    skip_cleared_at = time.time()
    cycle_num = 0
    next_live_events_at = 0.0
    next_m3u_refresh_at = 0.0

    # Startup: always fresh — delete old M3U, empty state, fetch live events on cycle #1.
    # Later cycles keep/update the M3U built in this run (cookie refresh, add/remove).
    event_state = {}
    if os.path.isfile(FHD_M3U_FILE):
        try:
            os.remove(FHD_M3U_FILE)
            print(f"{YELLOW}✓ Startup fresh: deleted old {FHD_M3U_FILE} (will rebuild from live API){RESET}")
        except Exception as e:
            print(f"{YELLOW}⚠ Could not delete old M3U: {e} — starting with empty state{RESET}")
            try:
                open(FHD_M3U_FILE, "w", encoding="utf-8").write("#EXTM3U\n")
            except Exception:
                pass

    # preload + validate 4K token pool (separate folder, rotate like FHD)
    try:
        _k4 = load_4k_tokens()
        if _k4:
            print(f"{GREEN}✓ 4K tokens loaded: {len(_k4)} from {TOKEN_4K_DIR}{RESET}")
            validate_4k_tokens(_k4)
        else:
            print(f"{YELLOW}⚠ No tokens in {TOKEN_4K_DIR}/ — 4K will fall back to FHD tokens{RESET}")
    except Exception as _e:
        print(f"{YELLOW}⚠ 4K token load: {_e}{RESET}")

    print(f"\n{BOLD_GREEN}Starting loop  (Ctrl+C to stop){RESET}")
    print(f"{GRAY}M3U file : {FHD_M3U_FILE}{RESET}")
    print(f"{GRAY}Tokens   : used only for NEW live events (once each){RESET}")
    print(
        f"{GRAY}Schedule: live/Sony every {LIVE_EVENT_INTERVAL_SEC}s · "
        f"M3U cookie refresh every {M3U_REFRESH_INTERVAL_SEC}s · "
        f"Cloudflare push after each update{RESET}"
    )
    print(f"{GRAY}Remove   : events gone from API after {EVENT_GRACE_MINUTES} min grace{RESET}\n")

    while True:
        cycle_start = time.time()
        ts = datetime.now(IST).strftime("%I:%M:%S %p")
        cycle_num += 1
        changed = False
        run_live_cycle = cycle_start >= next_live_events_at
        run_m3u_refresh = cycle_start >= next_m3u_refresh_at
        if run_live_cycle:
            next_live_events_at = cycle_start + LIVE_EVENT_INTERVAL_SEC
        if run_m3u_refresh:
            next_m3u_refresh_at = cycle_start + M3U_REFRESH_INTERVAL_SEC

        # Clear temporary skip list every 30 min
        if time.time() - skip_cleared_at >= 30 * 60:
            if skip_set:
                print(f"  {GRAY}↻ Cleared {len(skip_set)} skipped token(s){RESET}")
            skip_set.clear()
            skip_cleared_at = time.time()

        print(f"{BOLD_CYAN}[{ts}] Cycle #{cycle_num}{RESET}")
        _pending_refetch_keys = set()

        # ── A0. 24H cookie: always when missing / every 15h (no M3U required) ──
        try:
            age_24 = time.time() - float(_24H_COOKIE_CACHE.get("fetched_at") or 0)
            have_24 = bool(_24H_COOKIE_CACHE.get("token")) and age_24 < COOKIE_24H_TTL_SEC
            if not have_24:
                try:
                    with open("hdntl_24h.cache", "r", encoding="utf-8") as _cf:
                        disk = _strip_hdntl_prefix(_cf.read())
                    if disk and _hdntl_ttl_left(disk) > 5 * 3600:
                        _24H_COOKIE_CACHE["token"] = disk
                        _24H_COOKIE_CACHE["fetched_at"] = time.time()
                        have_24 = True
                        print(f"  {GREEN}✓ 24H cookie from cache (~{_hdntl_ttl_left(disk)/3600:.1f}h left){RESET}")
                except Exception:
                    pass
            if not have_24:
                print(f"  {DARK_MAGENTA}Fetching 24H cookie (c.py / 15h cycle)...{RESET}")
                tok24 = get_24h_cookie_cached(force=True)
                if tok24:
                    left = _hdntl_ttl_left(tok24)
                    print(f"  {GREEN}✓ 24H cookie ready (~{left/3600:.1f}h left, cache 15h){RESET}")
                else:
                    print(f"  {YELLOW}⚠ 24H cookie not available{RESET}")
            tok24 = _24H_COOKIE_CACHE.get("token") or ""
            if tok24 and os.path.isfile(FHD_M3U_FILE):
                try:
                    with open(FHD_M3U_FILE, "r", encoding="utf-8") as f:
                        m3u_24 = f.read()
                    if "24H" in m3u_24:
                        new_24, n24 = _rewrite_24h_blocks_in_m3u(m3u_24, tok24)
                        if n24:
                            with open(FHD_M3U_FILE, "w", encoding="utf-8") as f:
                                f.write(new_24)
                            print(f"  {GREEN}✓ 24H cookie applied to {n24} stream(s){RESET}")
                            changed = True
                except Exception:
                    pass
        except Exception as e:
            print(f"  {YELLOW}⚠ 24H refresh error: {e}{RESET}")

        # ── A. Refresh ALL existing hdntl cookies (h.py method — no tokens) ──
        if run_m3u_refresh and os.path.isfile(FHD_M3U_FILE):
            try:
                with open(FHD_M3U_FILE, "r", encoding="utf-8") as f:
                    m3u_content = f.read()
                print(f"  {DARK_MAGENTA}Refreshing hdntl cookies (CDN Set-Cookie)...{RESET}", end="", flush=True)
                new_content, n_ok, n_fail, failed_urls = refresh_all_hdntl_in_m3u(m3u_content)
                if n_ok or n_fail:
                    print(f"\r  {GREEN}✓ Cookie refresh: {n_ok} updated, {n_fail} failed{RESET}          ")
                    if n_ok:
                        print(f"  {GRAY}· guest Set-Cookie refreshed on {n_ok} FHD stream(s) (4K skipped){RESET}")
                    if n_ok:
                        with open(FHD_M3U_FILE, "w", encoding="utf-8") as f:
                            f.write(new_content)
                        old_state = event_state
                        event_state = _merge_state_after_parse(old_state, parse_m3u_events(new_content))
                        changed = True
                    # Cookie probe fail: keep existing tokens. Only full re-fetch if
                    # ALL tokens for an event are expired (<3 min left).
                    fail_keys = _event_keys_for_failed_urls(event_state, failed_urls or [])
                    now_ts = time.time()
                    recovered = set(event_state.keys()) - set(fail_keys)
                    for k in recovered:
                        if k in event_state and event_state[k].get("refresh_fail_since") is not None:
                            event_state[k]["refresh_fail_since"] = None
                    _pending_refetch_keys = set()
                    for k in fail_keys:
                        if k not in event_state:
                            continue
                        meta = event_state[k]
                        # Check if existing stream tokens still have life
                        still_alive = False
                        for block in meta.get("blocks") or []:
                            tok = extract_hdntl_from_url(block) or ""
                            try:
                                if tok and _hdntl_ttl_left(tok) > 180:
                                    still_alive = True
                                    break
                            except Exception:
                                pass
                        if still_alive:
                            # keep playing with current tokens — no mass re-fetch
                            continue
                        if meta.get("refresh_fail_since") is None:
                            meta["refresh_fail_since"] = now_ts
                        _pending_refetch_keys.add(k)
                        print(f"  {YELLOW}⏳ Tokens expired → API re-fetch: {meta.get('title1')}: {meta.get('title2')}{RESET}")
                else:
                    print(f"\r  {GRAY}· No token URLs to refresh{RESET}                    ")
                    _pending_refetch_keys = set()
            except Exception as e:
                print(f"\r  {YELLOW}⚠ Refresh error: {e}{RESET}")

        # ── A7. Refresh (7M) short API cookies (hot.py NORMAL FHD style) ──
        try:
            if run_m3u_refresh and os.path.isfile(FHD_M3U_FILE) and event_state:
                with open(FHD_M3U_FILE, "r", encoding="utf-8") as f:
                    m3u_7 = f.read()
                if "(7M)" in m3u_7:
                    # use any valid token for BFF API
                    _tok7 = ""
                    try:
                        for _tn, _ts, _tp in (valid_tokens or []):
                            if _tn not in expired_set and _tn not in skip_set:
                                _tok7 = _ts
                                break
                    except Exception:
                        pass
                    if not _tok7:
                        try:
                            _tok7 = (valid_tokens[0][1] if valid_tokens else "") or ""
                        except Exception:
                            _tok7 = ""
                    print(f"  {DARK_MAGENTA}Refreshing 7M cookies (API short hdnea)...{RESET}", end="", flush=True)
                    new_7, n7_ok, n7_fail = refresh_7m_cookies_in_m3u(
                        m3u_7, event_state, active_token=_tok7
                    )
                    if n7_ok or n7_fail:
                        print(f"  {GREEN}✓ 7M refresh: {n7_ok} updated, {n7_fail} failed{RESET}")
                        if n7_ok:
                            with open(FHD_M3U_FILE, "w", encoding="utf-8") as f:
                                f.write(new_7)
                            old_state = event_state
                            event_state = _merge_state_after_parse(old_state, parse_m3u_events(new_7))
                            changed = True
                    else:
                        print(f"  {GRAY}· No 7M streams to refresh{RESET}")
        except Exception as e:
            print(f"  {YELLOW}⚠ 7M refresh error: {e}{RESET}")

        # ── A8. Refresh 4K playback_host cookies (30M STABLE only) — not guest acl=/*
        try:
            if run_m3u_refresh and os.path.isfile(FHD_M3U_FILE):
                with open(FHD_M3U_FILE, "r", encoding="utf-8") as f:
                    m3u_4 = f.read()
                if "4K" in m3u_4:
                    print(f"  {DARK_MAGENTA}Refreshing 4K cookies (playback_host)...{RESET}", end="", flush=True)
                    new_4, n4_ok, n4_fail = refresh_4k_cookies_in_m3u(m3u_4, event_state)
                    if n4_ok or n4_fail:
                        print(f"  {GREEN}✓ 4K refresh: {n4_ok} updated, {n4_fail} failed{RESET}")
                        if n4_ok:
                            with open(FHD_M3U_FILE, "w", encoding="utf-8") as f:
                                f.write(new_4)
                            old_state = event_state
                            event_state = _merge_state_after_parse(old_state, parse_m3u_events(new_4))
                            changed = True
                    else:
                        print(f"  {GRAY}· No 4K streams to refresh{RESET}")
        except Exception as e:
            print(f"  {YELLOW}⚠ 4K refresh error: {e}{RESET}")

        # Live-event/Sony checks run every 60s. On the 70s-only ticks, push
        # immediately after the M3U cookie refresh and wait for the next task.
        if not run_live_cycle:
            if run_m3u_refresh and os.path.isfile(FHD_M3U_FILE):
                push_to_cloudflare_fhd(FHD_M3U_FILE, cf_worker_url, cf_api_token)
            next_due = min(next_live_events_at, next_m3u_refresh_at)
            wait_sec = max(0.1, next_due - time.time())
            next_ts = datetime.fromtimestamp(time.time() + wait_sec, tz=IST).strftime("%I:%M:%S %p")
            print(
                f"\n  {BOLD_YELLOW}Next scheduled task at {next_ts} — "
                f"waiting {wait_sec:.0f}s (M3U refresh={M3U_REFRESH_INTERVAL_SEC}s, "
                f"live/Sony={LIVE_EVENT_INTERVAL_SEC}s)...{RESET}\n"
            )
            time.sleep(wait_sec)
            continue

        # ── B. Pick a valid token for live-list + new-stream fetch ────────────
        still_valid = [t for t in valid_tokens if t[0] not in expired_set and t[0] not in skip_set]
        if not still_valid:
            still_valid = [t for t in valid_tokens if t[0] not in expired_set]
            if still_valid:
                print(f"  {YELLOW}All active tokens skipped — clearing skip list{RESET}")
                skip_set.clear()
                skip_cleared_at = time.time()
            else:
                print(f"  {RED}All tokens exhausted — waiting 60s{RESET}")
                time.sleep(60)
                continue

        tok_idx = get_time_based_token_index(still_valid)
        tok_num, tok_str, tok_path = still_valid[tok_idx]
        tok_label = f"token{tok_num}.txt" if tok_num else os.path.basename(tok_path)

        # p.py style: only drop on confirmed "bad"; ok/unknown both usable → ✓
        print(f"  Token for discovery: {tok_label}", end=" ", flush=True)
        if check_token_valid_fast(tok_str) == "bad":
            print(f"{RED}✗ EXPIRED{RESET}")
            expired_set.add(tok_num)
            skip_set.discard(tok_num)
            try:
                cache_path = _TOKEN_VALID_CACHE_FILE
                blob = {"ts": time.time(), "map": {}}
                if os.path.isfile(cache_path):
                    with open(cache_path, "r", encoding="utf-8") as f:
                        blob = json.load(f)
                mp = dict(blob.get("map") or {})
                mp[(tok_str or "")[:64]] = "bad"
                with open(cache_path, "w", encoding="utf-8") as f:
                    json.dump({"ts": time.time(), "map": mp}, f)
            except Exception:
                pass
            time.sleep(2)
            continue
        print(f"{GREEN}✓{RESET}")
        _ACTIVE_TOKEN_OVERRIDE = tok_str

        # ── C. Fetch current live events ─────────────────────────────────────
        print(f"  {DARK_MAGENTA}Checking live events...{RESET}", end="", flush=True)
        live_events, ev_err = fetch_all_live()
        print(f"\r  {GREEN}✓ {len(live_events)} live event(s) from API{RESET}            ")
        if ev_err:
            print(f"  {YELLOW}⚠ API error: {ev_err}{RESET}")

        live_keys = set()
        live_by_key = {}
        _deduped_live = []
        for ev in live_events:
            t1, t2, u = ev[:3]
            key = _normalize_event_key(t1, t2, u)
            if key in live_keys:
                continue  # drop duplicate sports/title feed
            live_keys.add(key)
            live_by_key[key] = ev
            _deduped_live.append(ev)
        live_events = _deduped_live

        if live_events:
            for i, ev in enumerate(live_events, 1):
                t1, t2, u = ev[:3]
                cid = _content_id_from_url(u)
                # show contentId when same title appears twice (Tamil vs Telugu BBS etc.)
                extra = f"  [{cid}]" if cid else ""
                print(f"  {BOLD_GREEN}{{{i}}}{RESET} {WHITE}{t1}: {t2}{extra}{RESET}")

        # ── D. NEW events → fetch streams once and append to M3U ─────────────
        # Match by contentId/source_url so LIVE SHOW keys stay stable across M3U re-parse
        new_keys = []
        for k in live_keys:
            ev = live_by_key[k]
            t1, t2, u = ev[:3]
            existing = _live_event_present(event_state, t1, t2, u)
            if existing:
                # already tracked — refresh identity / source_url under live key
                meta = event_state.pop(existing) if existing != k else event_state.get(k)
                if meta is None:
                    continue
                meta["title1"] = t1
                meta["title2"] = t2
                meta["source_url"] = u
                meta["last_seen"] = time.time()
                meta["missing_since"] = None
                event_state[k] = meta
            else:
                new_keys.append(k)
        if new_keys:
            print(f"  {BOLD_YELLOW}★ {len(new_keys)} NEW event(s) — fetching streams...{RESET}")

            def _fetch_one(key):
                ev = live_by_key[key]
                t1, t2, url = ev[:3]
                pre_logo = ev[3] if len(ev) > 3 else ""
                entries, logo = fetch_event_fhd_entries(t2, url)
                try:
                    k4 = fetch_event_4k_entries(t2, url)
                    if k4:
                        entries = list(entries or []) + list(k4)
                        print(f"  {GREEN}✓ 4K streams: {len(k4)}{RESET}")
                except Exception as _e4:
                    print(f"  {YELLOW}⚠ 4K fetch: {_e4}{RESET}")
                # ✅ API -h logo wins; skip resolver
                if pre_logo and _is_h_logo_path(pre_logo):
                    final_logo = pre_logo
                elif logo and _is_h_logo_path(logo):
                    final_logo = logo
                else:
                    try:
                        final_logo = resolve_event_logo(t1, t2, url, pre_logo or logo or "")
                    except Exception:
                        final_logo = pre_logo or logo or ""
                return key, t1, t2, final_logo, entries

            with ThreadPoolExecutor(max_workers=min(4, len(new_keys))) as ex:
                futs = {ex.submit(_fetch_one, k): k for k in new_keys}
                for fut in as_completed(futs):
                    key, t1, t2, logo, entries = fut.result()
                    if not entries:
                        print(f"  {YELLOW}⚠{RESET} {t1}: {t2} → no streams (will retry later)")
                        continue
                    ok = append_event_blocks_to_m3u(FHD_M3U_FILE, t1, t2, logo, entries, source_url=live_by_key[key][2] if key in live_by_key else "")
                    if ok:
                        old_state = event_state
                        with open(FHD_M3U_FILE, "r", encoding="utf-8") as f:
                            event_state = _merge_state_after_parse(old_state, parse_m3u_events(f.read()))
                        # key may differ after parse (category groups) — resolve safely
                        _ek = key if key in event_state else None
                        if _ek is None:
                            _src = ""
                            try:
                                _src = live_by_key[key][2]
                            except Exception:
                                pass
                            _want = _normalize_event_key(t1, t2, _src)
                            for _k, _m in event_state.items():
                                _murl = _m.get("source_url") or ""
                                if _normalize_event_key(_m.get("title1") or "", _m.get("title2") or "", _murl) == _want:
                                    _ek = _k
                                    break
                                if _src and _murl and _src.split("?")[0] == _murl.split("?")[0]:
                                    _ek = _k
                                    break
                        if _ek is None:
                            # create entry from what we just wrote
                            event_state[key] = {
                                "title1": t1,
                                "title2": t2,
                                "logo": logo or "",
                                "blocks": [],
                                "last_seen": time.time(),
                                "missing_since": None,
                            }
                            _ek = key
                        # Force stable live key + page source_url (contentId) so next cycle
                        # does not treat this LIVE SHOW as NEW again
                        src_url = ""
                        try:
                            src_url = live_by_key[key][2]
                        except Exception:
                            src_url = ""
                        meta = event_state.pop(_ek)
                        meta["title1"] = t1
                        meta["title2"] = t2
                        meta["logo"] = logo or meta.get("logo") or ""
                        meta["source_url"] = src_url
                        meta["last_seen"] = time.time()
                        meta["missing_since"] = None
                        meta["refresh_fail_since"] = None
                        event_state[key] = meta
                        changed = True
                        print(f"  {GREEN}✓ ADDED{RESET} {t1}: {t2} → {len(entries)} stream(s)")
                    else:
                        print(f"  {RED}✗ Failed to append {t1}: {t2}{RESET}")
        else:
            print(f"  {GRAY}· No new events{RESET}")

        # ── D2. Cookie-refresh FAILED events → re-fetch with real tokens ─────
        # Immediate on fail; also retry sustained fails every 2 min
        REFRESH_FAIL_GRACE_SEC = 0
        REFETCH_INTERVAL_SEC = 2 * 60
        now_ts = time.time()
        refetch_candidates = set(_pending_refetch_keys)
        for k, meta in list(event_state.items()):
            fail_since = meta.get("refresh_fail_since")
            if fail_since is None:
                continue
            age = now_ts - fail_since
            last_rf = meta.get("last_refetch") or 0
            if (now_ts - last_rf) >= REFETCH_INTERVAL_SEC:
                refetch_candidates.add(k)
                print(f"  {YELLOW}⏱ Cookie fail {age/60:.0f}m → API token re-fetch: "
                      f"{meta.get('title1')}: {meta.get('title2')}{RESET}")
        if refetch_candidates:
            keys_list = [k for k in list(refetch_candidates) if k in event_state]
            def _rf_one(k):
                return k, _refetch_event_streams(k, event_state[k], live_by_key, event_state, FHD_M3U_FILE)
            with ThreadPoolExecutor(max_workers=min(3, max(1, len(keys_list)))) as _rf_ex:
                _rf_futs = [_rf_ex.submit(_rf_one, k) for k in keys_list]
                for _f in as_completed(_rf_futs):
                    try:
                        k, ok = _f.result()
                    except Exception:
                        continue
                    if ok:
                        changed = True
                        event_state[k]["refresh_fail_since"] = None
                        event_state[k]["last_refetch"] = time.time()
                    else:
                        if event_state[k].get("refresh_fail_since") is None:
                            event_state[k]["refresh_fail_since"] = now_ts

        # Mark still-present events as seen (by live key OR contentId)
        now = time.time()
        live_cids = set()
        for key in live_keys:
            try:
                live_cids.add(_content_id_from_url(live_by_key[key][2]))
            except Exception:
                pass
            if key in event_state:
                event_state[key]["last_seen"] = now
                event_state[key]["missing_since"] = None
                try:
                    event_state[key]["source_url"] = live_by_key[key][2]
                except Exception:
                    pass
        for key, meta in list(event_state.items()):
            cid = _content_id_from_url(meta.get("source_url") or "")
            if cid and cid in live_cids:
                meta["last_seen"] = now
                meta["missing_since"] = None

        # Drop M3U-parse ghost keys (title1="LIVE SHOW: 24/7", no page source_url)
        # These false-trigger "Missing from API" while real entries under live keys exist.
        ghost_keys = []
        for key, meta in list(event_state.items()):
            cid = _content_id_from_url(meta.get("source_url") or "")
            if key in live_keys or (cid and cid in live_cids):
                continue
            t1 = (meta.get("title1") or "")
            has_src = bool((meta.get("source_url") or "").strip())
            is_category_ghost = t1.upper().startswith("LIVE SHOW") and "24/7" in t1
            if (not has_src) or is_category_ghost:
                # If a live key already covers same title2, pure ghost → drop silently
                t2n = _normalize_event_key("", meta.get("title2") or "", "")
                covered = False
                for lk, ev in live_by_key.items():
                    if _normalize_event_key("", ev[1], "") == t2n and lk in event_state:
                        covered = True
                        break
                if covered or not has_src:
                    ghost_keys.append(key)
        for gk in ghost_keys:
            event_state.pop(gk, None)
        if ghost_keys:
            print(f"  {GRAY}· Cleared {len(ghost_keys)} stale M3U key(s){RESET}")

        # ── E. Events missing from API → grace then remove ───────────────────
        to_remove = []
        for key, meta in list(event_state.items()):
            cid = _content_id_from_url(meta.get("source_url") or "")
            still_live = (key in live_keys) or (cid and cid in live_cids)
            if still_live:
                meta["missing_since"] = None
                continue
            if meta.get("missing_since") is None:
                meta["missing_since"] = now
                print(f"  {YELLOW}⏳ Missing from API (grace starts): {meta['title1']}: {meta['title2']}{RESET}")
            else:
                gone_for = (now - meta["missing_since"]) / 60.0
                if gone_for >= EVENT_GRACE_MINUTES:
                    to_remove.append(key)
                    print(f"  {RED}🗑 Removing (gone {gone_for:.0f}m): {meta['title1']}: {meta['title2']}{RESET}")
                else:
                    left = EVENT_GRACE_MINUTES - gone_for
                    print(f"  {GRAY}· Still missing {meta['title1']}: {meta['title2']} "
                          f"({left:.0f}m left in grace){RESET}")

        if to_remove:
            for key in to_remove:
                del event_state[key]
            if rebuild_m3u_from_events(event_state, FHD_M3U_FILE):
                changed = True
                print(f"  {GREEN}✓ M3U rewritten after removals ({len(event_state)} events left){RESET}")

        _ACTIVE_TOKEN_OVERRIDE = None

        # ── S. SonyLiv live events FIRST (so CF push includes Sony) ─────────
        try:
            sony_changed = sony_auto_cycle(FHD_M3U_FILE)
            if sony_changed:
                changed = True
        except Exception as _sony_err:
            print(f"  {YELLOW}⚠ Sony cycle error: {_sony_err}{RESET}")

        # ── F. Upload to Cloudflare (Hotstar + Sony combined M3U) ────────────
        if os.path.isfile(FHD_M3U_FILE):
            push_to_cloudflare_fhd(FHD_M3U_FILE, cf_worker_url, cf_api_token)

        # ── G. Push after Hotstar + Sony, then wait for the next schedule ─────
        next_due = min(next_live_events_at, next_m3u_refresh_at)
        wait_sec = max(0.1, next_due - time.time())
        elapsed = time.time() - cycle_start
        next_ts = datetime.fromtimestamp(time.time() + wait_sec, tz=IST).strftime("%I:%M:%S %p")
        print(
            f"\n  {BOLD_YELLOW}Next scheduled task at {next_ts} — waiting {wait_sec:.0f}s "
            f"(took {elapsed:.0f}s; M3U refresh={M3U_REFRESH_INTERVAL_SEC}s, "
            f"live/Sony={LIVE_EVENT_INTERVAL_SEC}s)...  (Ctrl+C to stop){RESET}\n"
        )
        try:
            time.sleep(wait_sec)
        except KeyboardInterrupt:
            print(f"\n{YELLOW}Stopped by user.{RESET}")
            _ACTIVE_TOKEN_OVERRIDE = None
            return


# =========================
# SINGLE-RUN MODE (pick event)
# =========================
def offer_m3u_creation(entries, title, match_no, stream_type, logo_url="", auto_hdntl=""):
    if not entries:
        return
    ans = input(f"\n{BOLD_CYAN}Save files? (y/n): {RESET}").strip().lower()
    if ans != 'y':
        return
    import hashlib
    _base = title.replace(' ', '_')
    hdntl_cookie = auto_hdntl
    if auto_hdntl:
        print(f"{GREEN}✓ Cookie auto-extracted, press Enter to use or paste new:{RESET}")
        print(f"{GRAY}hdntl={auto_hdntl[:60]}...{RESET}")
    raw_cookie = input(f"{BOLD_CYAN}Cookie : {RESET}").strip()
    if raw_cookie:
        if raw_cookie.startswith("hdntl="):
            hdntl_cookie = raw_cookie[len("hdntl="):]
        else:
            _m = re.search(r'hdntl=([^\s;&|]+)', raw_cookie)
            hdntl_cookie = _m.group(1) if _m else raw_cookie
    # txt
    with open(_base + ".txt", "w", encoding="utf-8") as f:
        f.write(f"# Generated: {datetime.now(IST).strftime('%Y-%m-%d %I:%M:%S %p')}\n\n")
        for entry in entries:
            name, url = entry[0], entry[1]
            final_url = url
            if hdntl_cookie and "hdntl=" not in url:
                sep = "&" if "?" in url else "?"
                final_url = url + sep + f"hdntl={hdntl_cookie}"
            f.write(f"\n{name}\n{final_url}\n")
    print(f"{GREEN}✓ Saved {_base}.txt{RESET}")
    # m3u
    with open(_base + ".m3u", "w", encoding="utf-8") as f:
        f.write("#EXTM3U\n# Playlist Created By @rtxcric\n")
        f.write(f"# Title: {title}\n# Generated: {datetime.now(IST).strftime('%Y-%m-%d %I:%M:%S %p')}\n\n")
        for entry in entries:
            if len(entry) >= 4:
                lang, url, is_hdr, drm_details = entry[:4]
            else:
                lang, url, is_hdr = entry[:3]
                drm_details = {}
            tvg_id = str(int(hashlib.md5(url.encode()).hexdigest(), 16) % 9999999999)
            label  = f"{lang} FHD HDR" if is_hdr else f"{lang} FHD"
            tok    = hdntl_cookie or extract_hdntl_from_url(url) or ""
            f.write(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{title}" group-title="{title}", {label} @rtxcric\n')
            _drm_keys = list(drm_details.get("keys") or [])
            if drm_details.get("is_drm") or ".mpd" in (url or "").lower():
                f.write("#KODIPROP:inputstream.adaptive.manifest_type=mpd\n")
                if _drm_keys:
                    f.write("#KODIPROP:inputstream.adaptive.license_type=clearkey\n")
                    f.write(f"#KODIPROP:inputstream.adaptive.license_key={','.join(_drm_keys)}\n")
            if not _drm_keys:
                _ck_m = re.search(r"(?:drmLicense|drm_license)=([0-9a-fA-F:,]+)", url or "")
                if _ck_m:
                    _parsed = _ck_m.group(1).strip().rstrip("&|")
                    f.write("#KODIPROP:inputstream.adaptive.manifest_type=mpd\n")
                    f.write("#KODIPROP:inputstream.adaptive.license_type=clearkey\n")
                    f.write(f"#KODIPROP:inputstream.adaptive.license_key={_parsed}\n")
            if not tok:
                _tok_m = re.search(r"(?:Cookie|cookie)=hdntl=([^&|]+)", url or "")
                if _tok_m:
                    tok = unquote(_tok_m.group(1).strip())
            _eh = f'{{"Origin":"{M3U_ORIGIN}","Referer":"{M3U_REFERER}"'
            if tok:
                _eh += f',"Cookie":"hdntl={tok}"'
            _eh += '}'
            f.write(f'#EXTHTTP:{_eh}\n')
            if tok:
                f.write(f"#EXTVLCOPT:http-cookie=hdntl={tok}\n")
            f.write(f'#EXTVLCOPT:http-extra-headers=Origin: {M3U_ORIGIN}\n')
            f.write(f'#EXTVLCOPT:http-referrer={M3U_REFERER}\n')
            f.write(f'#EXTVLCOPT:http-user-agent={M3U_USER_AGENT}\n')
            f.write(f"{url}\n")
    print(f"{GREEN}✓ Saved {_base}.m3u{RESET}")


def option_fhd_heavy_main(input_url: str):
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL!{RESET}")
        return
    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)
    print(f"{DARK_MAGENTA}FETCHING STREAMS... PLEASE WAIT{RESET}")
    entries, logo_url = fetch_event_fhd_entries(title, input_url)
    if not entries:
        print(f"{YELLOW}No streams found.{RESET}")
        return
    print(f"\n{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")
    first_cookie = ""
    for entry in entries:
        lname, final_url, is_hdr = entry[:3]
        htag = " HDR" if is_hdr else ""
        if not first_cookie:
            first_cookie = extract_hdntl_from_url(final_url.split("|")[0])
        print(f"{BOLD_CYAN}{lname}{htag}{RESET}")
        print(f"{GREEN}{final_url}{RESET}")
    if first_cookie:
        print(f"\n{BOLD_GREEN}COOKIE : {RESET}{CYAN}hdntl={first_cookie}{RESET}")
    offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=first_cookie or "")


# =========================
# MAIN
# =========================
def main():
    # ── Initialize proxy FIRST — required for ALL network calls ───────────────
    _init_proxy()

    # ── CLI: python fhdp.py <url>  →  single event mode ─────────────────────
    if len(sys.argv) > 1 and sys.argv[1].startswith("http"):
        option_fhd_heavy_main(sys.argv[1])
        return

    # ── Auto-update mode (zero prompts) ──────────────────────────────────────
    auto_update_mode()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print(f"\n{YELLOW}Stopped.{RESET}")
