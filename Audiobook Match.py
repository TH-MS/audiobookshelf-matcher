"""
Audiobookshelf Matcher - review Audible metadata + cover art before committing
cover.jpg and metadata.json into an audiobook folder.

Layout: E:\\Audiobooks\\[Author]\\[Title]\\[file(s)]

Modes
  Single        : pick one book folder.
  Open Existing : open ONE folder that already has metadata.json (+ cover) and edit it.
  Batch extras  : "Commit all good matches" writes cover.jpg + metadata.json for every
                  confident match (skipping folders that already have both);
                  "Move Matched" moves every finished Author\\Book folder elsewhere.
  Batch  : pick your library root; the app finds every Author -> Title -> File(s)
           folder, searches Audible for ALL of them in the background, and lets you
           step through them with Back / Forward. Commit only ever applies to the
           book currently on screen.

Smart matching
  * Cleans folder/file names (underscores for colons, [MP3], (Unabridged), track
    numbers, "Author - Title", "Series 02 - Title", "Title, The", ASINs, ...)
  * Tries several query variants and region(s) until a confident match is found
  * Reads embedded audio tags (album / artist) as extra evidence
  * Scores every result against your folder names and sorts best-first

Covers
  * Full-size original is tried first, with a size ladder, retries and a disk cache
  * Falls back to other matching results, then to Apple Books artwork
  * "Find Covers..." shows every candidate side by side so you can pick one
  * ◀ ▶ arrows under the cover step through more candidates. Nothing extra is searched
    until an arrow is clicked (then Audible results, Apple Books and Open Library are
    queried once for that book); each image is only downloaded when you reach it.

Diagnostics: unexpected errors are written to
  %APPDATA%\\AudiobookshelfMatcher\\error.log   (and shown in the status bar)
"""
import hashlib
import html
import io
import json
import os
import queue
import re
import shutil
import threading
import time
import traceback
import unicodedata
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from difflib import SequenceMatcher
from pathlib import Path

import customtkinter as ctk
import requests
from PIL import Image
from tkinter import filedialog, messagebox

try:
    from mutagen import File as MutagenFile
    from mutagen.mp4 import MP4
except Exception:  # chapters / tags are optional
    MutagenFile = None
    MP4 = None

APP_NAME = "Audiobookshelf Matcher"
UA = {"User-Agent": "Mozilla/5.0 AudiobookshelfMatcher/1.3"}
REGIONS = {
    "Audible.com": "https://api.audible.com",
    "Audible.co.uk": "https://api.audible.co.uk",
}
RESPONSE_GROUPS = ("contributors,media,product_attrs,product_desc,"
                   "product_extended_attrs,series,category_ladders")
AUDIO_EXT = {".mp3", ".m4b", ".m4a", ".flac", ".ogg", ".opus", ".wma", ".aac"}
APP_DIR = Path(os.environ.get("APPDATA", Path.home())) / "AudiobookshelfMatcher"
CONFIG_PATH = APP_DIR / "config.json"
LOG_PATH = APP_DIR / "error.log"
COVER_DIR = APP_DIR / "covers"
MODE_SINGLE, MODE_BATCH, MODE_EDIT = "Single Book", "Batch", "Open Existing"

GOOD_SCORE = 0.80      # confident match
CHECK_SCORE = 0.55     # below this = low confidence
EARLY_EXIT = 0.88      # stop trying query variants once we beat this
MAX_VARIANTS = 8
PREFETCH_WORKERS = 4
COVER_PX = 230         # on-screen cover preview size
MIN_GOOD_COVER = 500   # px; below this we look for a better cover elsewhere
TARGET_PX = 2000       # a cover this big (usually 2400x2400) is "as large as it gets"
SIMILAR_ART = 25.0     # max mean pixel difference for "same artwork" (same art <= ~7, different >= ~60)
COVER_NAMES = ("cover.jpg", "cover.jpeg", "cover.png", "cover.webp", "folder.jpg",
               "folder.png", "front.jpg")


# --------------------------------------------------------------------------- #
# Generic helpers
# --------------------------------------------------------------------------- #
def log_error(text):
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {text}\n")
    except Exception:
        pass


def load_config():
    try:
        return json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}


def save_config(cfg):
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        CONFIG_PATH.write_text(json.dumps(cfg), encoding="utf-8")
    except Exception:
        pass


def html_to_text(s):
    if not s:
        return ""
    s = re.sub(r"(?i)<\s*br\s*/?>", "\n", s)
    s = re.sub(r"(?i)</\s*p\s*>", "\n\n", s)
    s = re.sub(r"<[^>]+>", "", s)
    s = html.unescape(s)
    return re.sub(r"\n{3,}", "\n\n", s).strip()


def split_list(text):
    text = (text or "").strip()
    if not text:
        return []
    parts = text.split(";") if ";" in text else text.split(",")
    return [p.strip() for p in parts if p.strip()]


def join_list(items):
    return "; ".join(items)


def none_if_empty(s):
    s = (s or "").strip()
    return s if s else None


def natural_key(p):
    name = p.name if isinstance(p, Path) else str(p)
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", name)]


def subdirs(path: Path):
    try:
        return sorted([d for d in path.iterdir()
                       if d.is_dir() and not d.name.startswith((".", "$"))],
                      key=natural_key)
    except Exception:
        return []


def audio_files(path: Path):
    try:
        return sorted([f for f in path.iterdir()
                       if f.is_file() and f.suffix.lower() in AUDIO_EXT], key=natural_key)
    except Exception:
        return []


def has_audio(path: Path):
    return bool(audio_files(path))


def scan_library(root: Path):
    """Find Author -> Title -> File(s) folders under root."""
    books = []
    for author in subdirs(root):
        for title in subdirs(author):
            if has_audio(title):
                books.append(title)
    if not books:  # maybe the user picked a single Author folder
        for title in subdirs(root):
            if has_audio(title):
                books.append(title)
    return books


# --------------------------------------------------------------------------- #
# Smart name cleaning
# --------------------------------------------------------------------------- #
YEAR_RE = re.compile(r"(?<!\d)(19\d{2}|20\d{2})(?!\d)")
ASIN_RE = re.compile(r"(?<![A-Z0-9])(B0[0-9A-Z]{8})(?![A-Z0-9])")
JUNK_RE = re.compile(
    r"(?i)\b(?:unabridged|abridged|audiobook|audio\s*book|mp3|m4b|m4a|aaxc?|flac|ogg|"
    r"retail|audible|\d{2,3}\s*kbps|cd\s*\d+|disc\s*\d+)\b")
PAREN_JUNK_RE = re.compile(
    r"(?i)\b(?:book|vol|volume|part|series|narrated|read by|unabridged|abridged)\b|#\d")
AUTH_JUNK_RE = re.compile(
    r"(?i)^(unknown|various( artists)?|audiobooks?|misc\w*|new|to ?do|sort.*|\d.*sort.*)$")


def _fix_chars(s):
    s = unicodedata.normalize("NFKC", s or "")
    for a, b in (("\u2019", "'"), ("\u2018", "'"), ("\u201c", '"'), ("\u201d", '"'),
                 ("\uff1a", ":"), ("\ua789", ":")):
        s = s.replace(a, b)
    return s


def normalize_author(raw):
    """'Bothwell, Matthew' -> 'Matthew Bothwell'; first of several; drop junk."""
    s = _fix_chars(raw).replace("_", " ")
    s = re.sub(r"\([^)]*\)|\[[^\]]*\]", " ", s)
    s = re.sub(r"\s+", " ", s).strip(" -")
    if not s or AUTH_JUNK_RE.match(s):
        return ""
    first = re.split(r"\s*(?:;|&|/|\+|\band\b|\bwith\b)\s*", s, maxsplit=1,
                     flags=re.I)[0].strip()
    parts = [p.strip() for p in first.split(",") if p.strip()]
    if len(parts) == 2 and parts[1].lower().rstrip(".") in ("jr", "sr", "ii", "iii", "iv"):
        first = f"{parts[0]} {parts[1]}"
    elif len(parts) == 2 and len(parts[0].split()) == 1:
        first = f"{parts[1]} {parts[0]}"
    elif parts:
        first = parts[0]
    first = re.sub(r"\b([A-Z])\.(?=[A-Za-z])", r"\1. ", first)
    first = re.sub(r"(?i)^(?:dr|prof|professor|sir|mr|mrs|ms)\.?\s+", "", first)
    return re.sub(r"\s+", " ", first).strip()


def clean_title(raw, author_raw=""):
    """Turn a messy folder name into a search-friendly title plus useful extras."""
    s = _fix_chars(raw)
    if " " not in s.strip() and len(re.findall(r"[._]", s)) >= 2:
        s = re.sub(r"[._]+", " ", s)          # The.Martian.2013 -> The Martian 2013
    info = {"asin": "", "year": "", "abridged": bool(re.search(r"(?i)(?<!un)abridged", s))}

    m = ASIN_RE.search(s)
    if m:
        info["asin"] = m.group(1)
        s = s.replace(m.group(1), " ")

    # year inside any bracket type
    for mo in re.finditer(r"[\(\[\{]\s*((?:19|20)\d{2})\s*[\)\]\}]", s):
        info["year"] = mo.group(1)
        break

    s = re.sub(r"\[[^\]]*\]|\{[^}]*\}", " ", s)

    def paren(mo):
        c = mo.group(1)
        if JUNK_RE.search(c) or PAREN_JUNK_RE.search(c) or YEAR_RE.fullmatch(c.strip()):
            return " "
        return mo.group(0)
    s = re.sub(r"\(([^)]*)\)", paren, s)
    s = JUNK_RE.sub(" ", s)

    # leading / trailing author ("Author - Title", "Title - Author", "Title by Author")
    cands = {c for c in (author_raw.strip(), normalize_author(author_raw)) if c}
    for c in sorted(cands, key=len, reverse=True):
        e = re.escape(c)
        s = re.sub(rf"(?i)^\s*{e}\s*[-\u2013_:]+\s*", "", s)
        s = re.sub(rf"(?i)\s*(?:[-\u2013_]+\s*|\s+by\s+){e}\s*$", "", s)

    # leading track / sort numbers: "01 - Title", "12. Title"
    s = re.sub(r"^\s*\d{1,3}\s*[-._)\u2013]\s+", "", s)
    s = re.sub(r"^\s*\d{1,3}\s*[-._)\u2013](?=[A-Za-z])", "", s)

    # separators: no spaces at all -> dots/underscores are spaces
    if " " not in s.strip() and re.search(r"[._]", s):
        s = re.sub(r"[._]+", " ", s)
    s = re.sub(r"_\s*-\s*_", " - ", s)
    s = re.sub(r"_\s+", ": ", s)      # Windows turned ':' into '_'
    s = s.replace("_", " ")
    s = re.sub(r"\s+", " ", s).strip(" -\u2013:_,.")

    # "Title, The" -> "The Title"
    mo = re.match(r"(?i)^(.+),\s*(the|an|a)$", s)
    if mo:
        s = f"{mo.group(2).capitalize()} {mo.group(1)}"

    parts_dash = [p.strip() for p in re.split(r"\s+[-\u2013\u2014]\s+", s) if p.strip()]
    main = re.split(r"\s*:\s+|\s+[-\u2013\u2014]\s+", s, maxsplit=1)[0].strip()
    if len(main) < 3:
        main = s

    alts = []
    if len(parts_dash) > 1:
        alts += [parts_dash[-1], parts_dash[0], " ".join(parts_dash[1:])]
    mo = re.match(r"(?i)^(.+?)\s+(?:book\s*)?\d+\s*[-\u2013:.]\s*(.+)$", s)   # "Series 02 - Title"
    if mo:
        alts.append(mo.group(2))
    t = re.sub(r"(?i)[\s,]*(?:book|vol(?:ume)?|part)\s*\d+\s*$|\s*#\d+\s*$", "", s).strip()
    if t and t != s:
        alts.append(t)

    mo = re.match(r"^(.+?)\s+((?:19|20)\d{2})$", s)       # "The Martian 2013"
    if mo and len(mo.group(1).split()) >= 1:
        alts.append(mo.group(1))
        info["year"] = info["year"] or mo.group(2)

    seen, clean_alts = {s.lower(), main.lower()}, []
    for a in alts:
        a = a.strip(" -\u2013:_,.")
        if len(a) >= 3 and a.lower() not in seen:
            seen.add(a.lower())
            clean_alts.append(a)

    info.update({"full": s, "main": main, "alts": clean_alts})
    return info


def prefill_fields(folder: Path):
    """What we show in the Search boxes for a folder (no disk / network access)."""
    author = normalize_author(folder.parent.name)
    return clean_title(folder.name, folder.parent.name)["full"], author


def read_tags(folder: Path):
    """Album / artist from the first audio file - extra evidence for matching."""
    out = {"titles": [], "authors": []}
    if MutagenFile is None:
        return out
    files = audio_files(folder)
    if not files:
        return out
    try:
        audio = MutagenFile(files[0], easy=True)
        tags = audio.tags if audio is not None else None
        if not tags:
            return out

        def g(k):
            try:
                v = tags.get(k)
                return str(v[0]).strip() if v else ""
            except Exception:
                return ""
        if g("album"):
            out["titles"].append(g("album"))
        if len(files) == 1 and g("title"):
            out["titles"].append(g("title"))
        for k in ("albumartist", "artist"):
            if g(k):
                out["authors"].append(g(k))
    except Exception:
        pass
    return out


def find_asin(folder: Path):
    names = [folder.name] + [f.name for f in audio_files(folder)[:30]]
    for n in names:
        m = ASIN_RE.search(n)
        if m:
            return m.group(1)
    return ""


# --------------------------------------------------------------------------- #
# Match scoring
# --------------------------------------------------------------------------- #
def norm(s):
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c)).lower()
    s = s.replace("&", " and ")
    s = re.sub(r"[^a-z0-9]+", " ", s)
    s = re.sub(r"\b(?:unabridged|abridged|audiobook)\b", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def sim(a, b):
    if not a or not b:
        return 0.0
    return SequenceMatcher(None, a, b).ratio()


def author_sim(a, b):
    a, b = norm(a), norm(b)
    ta, tb = " ".join(sorted(a.split())), " ".join(sorted(b.split()))
    return max(sim(a, b), sim(ta, tb))


def score_item(item, ref):
    pt_title = norm(item["title"])
    pt_main = norm(item["title"].split(":")[0])
    pt_full = norm(f"{item['title']} {item['subtitle']}")
    t = 0.0
    for rt in ref["titles"]:
        for pt in (pt_title, pt_main, pt_full):
            t = max(t, sim(rt, pt))

    if ref["authors"] and item["authors"]:
        a = max(author_sim(ra, pa) for ra in ref["authors"] for pa in item["authors"])
        score = 0.75 * t + 0.25 * a
    else:
        score = t * 0.9           # no author evidence either way

    if ref["year"] and item["year"] == ref["year"]:
        score += 0.03
    if item["abridged"] and not ref["abridged"]:
        score -= 0.05
    return max(0.0, min(1.0, score))


# --------------------------------------------------------------------------- #
# Audible access
# --------------------------------------------------------------------------- #
class BadRequest(Exception):
    pass


IMAGE_SIZES = "500,900,1215"      # ask Audible for its bigger renditions too


def http_get_json(url, params=None, allow_404=False):
    last = None
    for attempt in range(3):
        try:
            r = requests.get(url, params=params, headers=UA, timeout=20)
            if r.status_code == 404 and allow_404:
                return None
            if r.status_code == 400:
                raise BadRequest("HTTP 400")
            if r.status_code in (429, 500, 502, 503, 504):
                raise requests.HTTPError(f"HTTP {r.status_code}")
            r.raise_for_status()
            return r.json()
        except BadRequest:
            raise
        except Exception as ex:
            last = ex
            time.sleep(1.5 * (attempt + 1))
    raise last


def audible_get(url, params, allow_404=False):
    """GET with the larger image sizes requested; quietly retry without if refused."""
    try:
        return http_get_json(url, {**params, "image_sizes": IMAGE_SIZES}, allow_404)
    except BadRequest:
        return http_get_json(url, params, allow_404)


def audible_search(base, title="", author="", keywords=""):
    params = {"num_results": 10, "products_sort_by": "Relevance",
              "response_groups": RESPONSE_GROUPS}
    if keywords:
        params["keywords"] = keywords
    else:
        if title:
            params["title"] = title
        if author:
            params["author"] = author
    return (audible_get(base + "/1.0/catalog/products", params) or {}).get("products", [])


def audible_by_asin(base, asin):
    data = audible_get(f"{base}/1.0/catalog/products/{asin}",
                       {"response_groups": RESPONSE_GROUPS}, allow_404=True)
    return (data or {}).get("product")


def parse_product(p, region):
    series = []
    for s in p.get("series") or []:
        name = s.get("title")
        if name:
            seq = s.get("sequence")
            series.append(f"{name} #{seq}" if seq else name)

    genres = []
    for lad in p.get("category_ladders") or []:
        for node in lad.get("ladder") or []:
            n = node.get("name")
            if n and n not in genres:
                genres.append(n)

    images = p.get("product_images") or {}
    cover = None
    if images:
        key = max(images, key=lambda k: int(k) if str(k).isdigit() else 0)
        cover = images[key]

    date = p.get("release_date") or p.get("issue_date") or ""
    desc = p.get("publisher_summary") or p.get("merchandising_summary") or ""
    lang = (p.get("language") or "").strip()

    return {
        "region": region,
        "title": p.get("title") or "",
        "subtitle": p.get("subtitle") or "",
        "authors": [a["name"] for a in p.get("authors") or [] if a.get("name")],
        "narrators": [a["name"] for a in p.get("narrators") or [] if a.get("name")],
        "series": series,
        "genres": genres,
        "year": date[:4],
        "date": date,
        "publisher": p.get("publisher_name") or "",
        "language": lang.capitalize(),
        "asin": p.get("asin") or "",
        "isbn": p.get("isbn") or "",
        "abridged": (p.get("format_type") or "").lower() == "abridged",
        "explicit": bool(p.get("is_adult_product")),
        "description": html_to_text(desc),
        "cover_url": cover,
        "score": 0.0,
    }


def smart_search(regions, title_raw, author_raw, folder=None, exact=False):
    """
    Try several cleaned query variants across regions until a confident match is
    found. Returns (results sorted best-first, [error strings]).
    """
    ct = clean_title(title_raw, author_raw)
    author = normalize_author(author_raw)
    tags = read_tags(folder) if folder else {"titles": [], "authors": []}
    asin = ct["asin"] or (find_asin(folder) if folder else "")

    # ---- reference strings used for scoring ----
    ref_titles = [ct["full"], ct["main"]] + ct["alts"]
    tag_titles = []
    for t in tags["titles"]:
        c = clean_title(t, author_raw)
        tag_titles += [c["full"], c["main"]]
    ref_titles += tag_titles
    ref = {
        "titles": [x for x in dict.fromkeys(norm(t) for t in ref_titles) if x],
        "authors": [a for a in dict.fromkeys(
            [author] + [normalize_author(a) for a in tags["authors"]]) if a],
        "year": ct["year"],
        "abridged": ct["abridged"],
    }

    # ---- query variants: (title, author, keywords) ----
    variants, seen = [], set()

    def add(t="", a="", kw=""):
        t, a, kw = (t or "").strip(), (a or "").strip(), (kw or "").strip()
        if not (t or a or kw):
            return
        k = (t.lower(), a.lower(), kw.lower())
        if k not in seen:
            seen.add(k)
            variants.append((t, a, kw))

    if exact:
        add(title_raw, author_raw)
    add(ct["full"], author)
    add(ct["main"], author)
    for alt in ct["alts"]:
        add(alt, author)
    for t in tag_titles[:2]:
        add(t, normalize_author(tags["authors"][0]) if tags["authors"] else author)
    add(ct["full"])
    add(ct["main"])
    for alt in ct["alts"]:
        add(alt)
    add(kw=f"{ct['full']} {author}")
    variants = variants[:MAX_VARIANTS]

    results, errors, seen_items = [], [], set()

    def ingest(p, reg, forced=None):
        item = parse_product(p, reg)
        key = (item["asin"], reg)
        if key in seen_items:
            return
        seen_items.add(key)
        item["score"] = forced if forced is not None else score_item(item, ref)
        results.append(item)

    # ---- direct ASIN hit (folder / file name contains an ASIN) ----
    if asin:
        for reg in regions:
            try:
                p = audible_by_asin(REGIONS[reg], asin)
                if p:
                    ingest(p, reg, forced=1.0)
            except Exception as ex:
                errors.append(f"{reg}: {ex}")

    for (t, a, kw) in variants:
        for reg in regions:
            try:
                for p in audible_search(REGIONS[reg], t, a, kw):
                    ingest(p, reg)
            except Exception as ex:
                errors.append(f"{reg}: {ex}")
        if results and max(r["score"] for r in results) >= EARLY_EXIT:
            break

    results.sort(key=lambda r: -r["score"])
    return results[:15], list(dict.fromkeys(errors))


# --------------------------------------------------------------------------- #
# Cover art: robust download, size ladder, fallbacks
# --------------------------------------------------------------------------- #
def _cache_path(url):
    return COVER_DIR / (hashlib.sha1(url.encode("utf-8")).hexdigest() + ".bin")


def download_image(url, retries=3):
    """Download + validate one image (disk-cached). Returns (bytes, (w, h))."""
    cp = _cache_path(url)
    try:
        if cp.exists():
            data = cp.read_bytes()
            img = Image.open(io.BytesIO(data))
            img.load()
            return data, img.size
    except Exception:
        pass
    last = None
    for attempt in range(retries):
        try:
            r = requests.get(url, headers=UA, timeout=30)
            if r.status_code in (403, 404, 410):
                raise FileNotFoundError(f"HTTP {r.status_code} for {url}")
            r.raise_for_status()
            data = r.content
            img = Image.open(io.BytesIO(data))
            img.load()
            if min(img.size) < 50:
                raise ValueError("image too small")
            try:
                COVER_DIR.mkdir(parents=True, exist_ok=True)
                cp.write_bytes(data)
            except Exception:
                pass
            return data, img.size
        except FileNotFoundError:
            raise                       # a missing size variant: don't retry
        except Exception as ex:
            last = ex
            time.sleep(1.0 + attempt)
    raise last


def fetch_first_good(urls, good=TARGET_PX, first_wins=False):
    """
    Try URLs in order and keep the biggest valid image. Stops early once an image is
    >= `good` px. With first_wins=True a successful FIRST url is taken as the original
    (Amazon's un-suffixed URL), so we never swap it for an up-scaled copy.
    """
    best, last = None, None
    for i, u in enumerate(urls):
        try:
            data, size = download_image(u)
        except Exception as ex:
            last = ex
            continue
        if best is None or size[0] * size[1] > best[1][0] * best[1][1]:
            best = (data, size)
        if (first_wins and i == 0) or min(size) >= good:
            break
    if best is None:
        raise RuntimeError(f"cover download failed ({last})")
    return best


def amazon_ladder(url):
    """Full-size original first (strip ._SL500_ style suffix), then the given URL,
    then explicit size variants as a last resort."""
    base = re.sub(r"\._[^/.]*_(?=\.\w+$)", "", url)
    urls = [base, url]
    if "media-amazon" in url or "/images/I/" in url:
        for n in (2400, 1500, 1000):
            urls.append(re.sub(r"(\.\w+)$", rf"._SL{n}_\1", base))
    return list(dict.fromkeys(urls))


def itunes_candidates(title, author, limit=4):
    """Apple Books / iTunes audiobook artwork (high-res) as a backup cover source."""
    out, seen = [], set()
    split_main = lambda t: re.split(r"\s*:\s+|\s+[-\u2013\u2014]\s+", t or "", maxsplit=1)[0]
    main = norm(split_main(title))
    for country in ("us", "gb"):
        try:
            r = requests.get("https://itunes.apple.com/search",
                             params={"term": f"{title} {author}".strip(), "media": "audiobook",
                                     "limit": 6, "country": country},
                             headers=UA, timeout=20)
            r.raise_for_status()
            found = r.json().get("results", [])
        except Exception:
            continue
        for it in found:
            art = it.get("artworkUrl100") or it.get("artworkUrl60")
            name = it.get("collectionName") or it.get("trackName") or ""
            if not art:
                continue
            if sim(main, norm(split_main(name))) < 0.6 and sim(norm(title), norm(name)) < 0.6:
                continue
            ladder = [re.sub(r"/\d+x\d+(?:bb|sr|cc)?\.(jpg|png)$", rf"/{n}x{n}bb.\1", art)
                      for n in (2400, 1400, 600)]
            if ladder[-1] in seen:
                continue
            seen.add(ladder[-1])
            out.append({"label": f"Apple Books ({country.upper()}) — {name}", "urls": ladder})
            if len(out) >= limit:
                return out
    return out


def same_artwork(a_bytes, b_bytes):
    """True if two images are the same picture (even at different sizes / compression)."""
    try:
        def sig(b):
            im = Image.open(io.BytesIO(b)).convert("RGB").resize((24, 24), Image.LANCZOS)
            return im.tobytes()
        pa, pb = sig(a_bytes), sig(b_bytes)
        diff = sum(abs(x - y) for x, y in zip(pa, pb)) / len(pa)
        return diff < SIMILAR_ART
    except Exception:
        return False


def resolve_cover(item, fallbacks=(), title="", author=""):
    """
    Best (largest) cover for a result.
      1. This result's own cover at full size (original first, then size variants).
      2. If that is still small (< 2000px), look for a bigger copy of the SAME artwork
         in other Audible editions and in Apple Books (compared visually, so a different
         edition's artwork is never swapped in by mistake).
      3. If Audible gave no usable cover at all, use the best matching Apple Books one.
    Returns (bytes, (w, h), source_label) or raises RuntimeError.
    """
    errors, seen = [], set()
    items = [item] + list(fallbacks)
    tag = lambda it: "UK" if it["region"].endswith("uk") else "US"
    pixels = lambda sz: sz[0] * sz[1]

    primary = None
    for it in items:
        url = it.get("cover_url")
        if not url or url in seen:
            continue
        seen.add(url)
        try:
            data, size = fetch_first_good(amazon_ladder(url), first_wins=True)
            primary = (data, size, f"Audible {tag(it)}")
            break
        except Exception as ex:
            errors.append(str(ex))
    if primary and min(primary[1]) >= TARGET_PX:
        return primary

    # ---- look for a larger version of the same picture elsewhere ----
    pool = []
    own = {item.get("cover_url")}
    for it in items[1:]:                                   # other Audible editions
        url = it.get("cover_url")
        if url and url not in own:
            own.add(url)
            pool.append((f"Audible {tag(it)}", amazon_ladder(url), url, True))
    try:
        t = title or item.get("title", "")
        a = author or (item["authors"][0] if item.get("authors") else "")
        for c in itunes_candidates(t, a):
            pool.append(("Apple Books", c["urls"], c["urls"][-1], False))
    except Exception as ex:
        errors.append(str(ex))

    best = primary
    done = set()
    for label, ladder, probe, first_wins in pool:
        if ladder[0] in done:
            continue
        done.add(ladder[0])
        try:
            if primary:                                   # cheap look at the small copy first
                small, _ = fetch_first_good([probe], good=1)
                if not same_artwork(primary[0], small):
                    continue
            data, size = fetch_first_good(ladder, first_wins=first_wins)
        except Exception as ex:
            errors.append(str(ex))
            continue
        if best is None or pixels(size) > pixels(best[1]):
            src = (f"{label} (same art as {primary[2]})" if primary else label)
            best = (data, size, src)
        if min(best[1]) >= TARGET_PX:
            break
    if best:
        return best
    raise RuntimeError("; ".join(dict.fromkeys(errors)) or "no cover available")


def openlibrary_candidates(title, author, limit=6):
    """Open Library covers (usually book/ebook art) as extra choices."""
    out = []
    split_main = lambda t: re.split(r"\s*:\s+|\s+[-\u2013\u2014]\s+", t or "", maxsplit=1)[0]
    main = norm(split_main(title))
    try:
        params = {"title": split_main(title), "limit": 10, "fields": "title,author_name,cover_i"}
        if author:
            params["author"] = author
        r = requests.get("https://openlibrary.org/search.json", params=params,
                         headers=UA, timeout=20)
        r.raise_for_status()
        for d in r.json().get("docs", []):
            cid, name = d.get("cover_i"), d.get("title") or ""
            if not cid or sim(main, norm(split_main(name))) < 0.6:
                continue
            out.append({"label": f"Open Library — {name}",
                        "urls": [f"https://covers.openlibrary.org/b/id/{cid}-L.jpg"]})
            if len(out) >= limit:
                break
    except Exception:
        pass
    return out


def collect_cover_candidates(results, title, author, broad=False):
    """
    Every distinct cover we can find for this book: covers of the matched Audible
    results, Apple Books artwork and Open Library. With broad=True we also run a
    title-only Audible search (like Audiobookshelf's cover search) for more variety.
    """
    cands, seen = [], set()

    def add_audible(r):
        url = r.get("cover_url")
        if not url:
            return
        ladder = amazon_ladder(url)
        if ladder[0] in seen:
            return
        seen.add(ladder[0])
        tag = "UK" if r["region"].endswith("uk") else "US"
        cands.append({"label": f"Audible {tag} — {r['title']} ({r['year']})", "urls": ladder,
                      "first_wins": True})

    for r in results[:15]:
        add_audible(r)

    if broad and title:
        for reg, base in REGIONS.items():
            try:
                for p in audible_search(base, title=title):
                    add_audible(parse_product(p, reg))
            except Exception:
                pass

    try:
        cands += itunes_candidates(title, author, limit=6)
    except Exception:
        pass
    cands += openlibrary_candidates(title, author)
    return cands


def build_chapters(folder: Path):
    """One chapter per file for multi-part, embedded chapters for m4b."""
    if MutagenFile is None:
        return []
    files = audio_files(folder)
    chapters = []
    try:
        if len(files) == 1 and files[0].suffix.lower() in (".m4b", ".m4a"):
            mp4 = MP4(files[0])
            total = float(mp4.info.length)
            embedded = list(getattr(mp4, "chapters", None) or [])
            if embedded:
                for i, ch in enumerate(embedded):
                    end = embedded[i + 1].start if i + 1 < len(embedded) else total
                    chapters.append({"id": i, "start": round(float(ch.start), 6),
                                     "end": round(float(end), 6), "title": ch.title})
            else:
                chapters.append({"id": 0, "start": 0, "end": round(total, 6),
                                 "title": files[0].stem})
        else:
            pos = 0.0
            for i, f in enumerate(files):
                audio = MutagenFile(f)
                dur = float(audio.info.length) if audio and audio.info else 0.0
                chapters.append({"id": i, "start": round(pos, 6),
                                 "end": round(pos + dur, 6), "title": f.stem})
                pos += dur
    except Exception:
        pass
    return chapters


# --------------------------------------------------------------------------- #
# Writing the book's files (shared by single Commit and "Commit all good matches")
# --------------------------------------------------------------------------- #
def has_cover(folder: Path):
    return any((folder / n).is_file() for n in COVER_NAMES)


def is_committed(folder: Path):
    """A finished book: it already has a metadata.json AND a cover file."""
    return (folder / "metadata.json").is_file() and has_cover(folder)


def atomic_write(path: Path, data: bytes):
    """Write via a temp file so an interrupted write never leaves a half-written file."""
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_bytes(data)
    os.replace(tmp, path)


def save_cover_jpg(data: bytes, path: Path):
    img = Image.open(io.BytesIO(data))
    if (img.format or "").upper() == "JPEG":
        atomic_write(path, data)
    else:
        buf = io.BytesIO()
        img.convert("RGB").save(buf, "JPEG", quality=95)
        atomic_write(path, buf.getvalue())


def compose_meta(f, abridged, explicit, description, published_date, chapters):
    """Build the Audiobookshelf metadata.json dict from form-style string fields."""
    return {
        "tags": split_list(f["tags"]),
        "chapters": chapters,
        "title": f["title"].strip(),
        "subtitle": none_if_empty(f["subtitle"]),
        "authors": split_list(f["authors"]),
        "narrators": split_list(f["narrators"]),
        "series": split_list(f["series"]),
        "genres": split_list(f["genres"]),
        "publishedYear": none_if_empty(f["year"]),
        "publishedDate": none_if_empty(published_date),
        "publisher": none_if_empty(f["publisher"]),
        "description": none_if_empty(description),
        "isbn": none_if_empty(f["isbn"]),
        "asin": none_if_empty(f["asin"]),
        "language": none_if_empty(f["language"]),
        "explicit": bool(explicit),
        "abridged": bool(abridged),
    }


def fields_from_item(r):
    """Form-style fields for an Audible result (what the screen would show for it)."""
    return {"title": r["title"], "subtitle": r["subtitle"], "authors": join_list(r["authors"]),
            "narrators": join_list(r["narrators"]), "series": join_list(r["series"]),
            "genres": join_list(r["genres"]), "tags": "", "year": r["year"],
            "publisher": r["publisher"], "language": r["language"], "asin": r["asin"],
            "isbn": r["isbn"]}


def write_job(job):
    """
    Commit one book from a prepared job. Only the missing pieces are written: an existing
    metadata.json or cover is never overwritten. If a cover is needed but none can be
    found, NOTHING is written for that book (so it never ends up half-done).
    """
    folder = job["folder"]
    cover = None
    if job["need_cover"]:
        cover = job.get("cover")
        if not cover:
            cover, _size, _src = resolve_cover(job["item"], job["fallbacks"],
                                               job["title"], job["author"])
    meta = None
    if job["need_meta"]:
        meta = compose_meta(job["fields"], job["abridged"], job["explicit"], job["desc"],
                            job["date"], build_chapters(folder))
    if cover:
        save_cover_jpg(cover, folder / "cover.jpg")
    if meta is not None:
        atomic_write(folder / "metadata.json",
                     json.dumps(meta, indent=2, ensure_ascii=False).encode("utf-8"))


# --------------------------------------------------------------------------- #
# Application
# --------------------------------------------------------------------------- #
class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")
        self.title(APP_NAME)
        self.geometry("1180x900")
        self.minsize(1050, 860)

        self.cfg = load_config()
        self.mode = MODE_SINGLE
        self.book_dir = None
        self.cover_bytes = None
        self.results = []
        self.result_labels = []
        self._published_date = ""
        self.gen = 0                      # invalidates stale background workers
        self.q = queue.Queue()            # worker -> UI thread messages
        self._cover_win = None
        self.cgen = 0                     # invalidates stale COVER workers only
        self.existing_meta = {}           # "Open Existing" mode: metadata.json as loaded
        self.existing_cover_bytes = None
        self._preview_win = None
        self.busy = False                 # a batch commit / move is running
        self.skipped = set()              # batch books the user discarded (excluded from Commit all)
        self.pf_summary = ""
        self.matched_count = 0
        self.cover_ctx = 0                # identifies the current cover-browsing session
        self.cc = {"state": "idle", "cands": [], "pos": 0, "hashes": set(), "pending": 1}

        # Cover images: the label must NEVER point at a freed Tk image, so we keep a
        # permanent placeholder plus a short history of the images shown.
        self._cover_refs = deque(maxlen=8)
        self.placeholder_img = ctk.CTkImage(
            light_image=Image.new("RGBA", (COVER_PX, COVER_PX), (0, 0, 0, 0)),
            dark_image=Image.new("RGBA", (COVER_PX, COVER_PX), (0, 0, 0, 0)),
            size=(COVER_PX, COVER_PX))

        # batch state
        self.all_books = []
        self.books = []
        self.index = -1
        self.cache = {}                   # str(path) -> snapshot of review state
        self.committed = set()
        self.batch_id = 0
        self.executor = None
        self.prefetch = {}                # str(path) -> {"results","errors"}
        self.pf_pending = set()
        self.pf_total = 0
        self.conf = {}                    # str(path) -> best score
        self.waiting_key = None

        self.columnconfigure(0, weight=0)
        self.columnconfigure(1, weight=1)
        self.rowconfigure(1, weight=1)

        self._build_top()
        self._build_left()
        self._build_form()
        self._build_bottom()
        self.set_mode(MODE_SINGLE)

        self.bind("<Alt-Left>", lambda e: self.go(-1))
        self.bind("<Alt-Right>", lambda e: self.go(1))
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(80, self._poll)

    # ------------------------- thread -> UI plumbing ------------------------- #
    def post(self, fn):
        self.q.put(fn)

    def _report(self, text, short):
        log_error(text)
        try:
            self.set_status(f"⚠ Internal error: {short}  (details in error.log)")
        except Exception:
            pass

    def report_callback_exception(self, exc, val, tb):
        """Tk calls this for exceptions in button handlers etc. - never hide them."""
        self._report("".join(traceback.format_exception(exc, val, tb)), str(val)[:120])

    def _poll(self):
        try:
            for _ in range(60):
                fn = self.q.get_nowait()
                try:
                    fn()
                except Exception as ex:
                    self._report(traceback.format_exc(), str(ex)[:120])
        except queue.Empty:
            pass
        self.after(80, self._poll)

    def on_close(self):
        self.batch_id += 1
        if self.executor:
            self.executor.shutdown(wait=False, cancel_futures=True)
        self.destroy()
        os._exit(0)

    # ---------------------------- UI construction ---------------------------- #
    def _build_top(self):
        bar = ctk.CTkFrame(self, corner_radius=10)
        bar.grid(row=0, column=0, columnspan=2, sticky="ew", padx=14, pady=(14, 8))
        bar.columnconfigure(2, weight=1)

        self.mode_btn = ctk.CTkSegmentedButton(bar, values=[MODE_SINGLE, MODE_BATCH, MODE_EDIT],
                                               command=self.set_mode)
        self.mode_btn.grid(row=0, column=0, padx=10, pady=10)
        self.pick_btn = ctk.CTkButton(bar, text="📁  Select Book Folder", width=200,
                                      command=self.pick_folder)
        self.pick_btn.grid(row=0, column=1, padx=6, pady=10)
        self.path_label = ctk.CTkLabel(bar, text="No folder selected", anchor="w",
                                       text_color=("gray30", "gray70"))
        self.path_label.grid(row=0, column=2, sticky="ew", padx=6)

        # Batch status strip (hidden outside batch mode). Back/Forward live in the bottom bar.
        self.nav = ctk.CTkFrame(bar, fg_color="transparent")
        self.nav.grid(row=1, column=0, columnspan=3, sticky="ew", padx=10, pady=(0, 10))
        self.nav.columnconfigure(0, weight=1)
        self.counter = ctk.CTkLabel(self.nav, text="", anchor="w",
                                    font=ctk.CTkFont(weight="bold"))
        self.counter.grid(row=0, column=0, sticky="ew", padx=(4, 12))
        self.move_btn = ctk.CTkButton(self.nav, text="📦  Move Matched", width=150,
                                      state="disabled", command=self.move_matched)
        self.move_btn.grid(row=0, column=1, padx=(6, 10))
        self.pf_label = ctk.CTkLabel(self.nav, text="", text_color=("gray30", "gray70"))
        self.pf_label.grid(row=0, column=2, padx=(6, 4))
        self.pf_bar = ctk.CTkProgressBar(self.nav, width=110)
        self.pf_bar.set(0)
        self.pf_bar.grid(row=0, column=3, padx=(0, 10))
        self.hide_done = ctk.CTkCheckBox(self.nav, text="Hide books with metadata.json",
                                         command=self.refilter)
        self.hide_done.grid(row=0, column=4, padx=6)

    def _build_left(self):
        left = ctk.CTkFrame(self, width=330, corner_radius=10)
        left.grid(row=1, column=0, sticky="ns", padx=(14, 7), pady=6)
        left.grid_propagate(False)
        left.columnconfigure(0, weight=1)

        self.cover_label = ctk.CTkLabel(left, text="No cover", image=self.placeholder_img,
                                        width=COVER_PX, height=COVER_PX,
                                        fg_color=("gray80", "gray20"), corner_radius=8)
        self.cover_label.grid(row=0, column=0, padx=16, pady=(14, 2))
        self._cover_refs.append(self.placeholder_img)
        self.cover_label.bind("<Button-1>", self.open_cover_preview)
        try:
            self.cover_label.configure(cursor="hand2")
        except Exception:
            pass
        self.res_label = ctk.CTkLabel(left, text="", text_color=("gray30", "gray70"))
        self.res_label.grid(row=1, column=0)

        # ◀ Cover 1 of N ▶  - searches for more covers only when clicked
        arrows = ctk.CTkFrame(left, fg_color="transparent")
        arrows.grid(row=2, column=0, sticky="ew", padx=16, pady=(2, 2))
        arrows.columnconfigure(1, weight=1)
        self.cover_prev_btn = ctk.CTkButton(arrows, text="◀", width=44,
                                            command=lambda: self.cover_step(-1))
        self.cover_prev_btn.grid(row=0, column=0)
        self.cover_nav_label = ctk.CTkLabel(arrows, text="Browse more covers",
                                            text_color=("gray30", "gray70"))
        self.cover_nav_label.grid(row=0, column=1, sticky="ew", padx=6)
        self.cover_next_btn = ctk.CTkButton(arrows, text="▶", width=44,
                                            command=lambda: self.cover_step(1))
        self.cover_next_btn.grid(row=0, column=2)

        cover_row = ctk.CTkFrame(left, fg_color="transparent")
        cover_row.grid(row=3, column=0, sticky="ew", padx=16, pady=(4, 2))
        cover_row.columnconfigure(0, weight=1)
        self.url_entry = ctk.CTkEntry(cover_row, placeholder_text="Image URL from the web")
        self.url_entry.grid(row=0, column=0, sticky="ew")
        ctk.CTkButton(cover_row, text="Load", width=56,
                      command=self.load_cover_url).grid(row=0, column=1, padx=(6, 0))

        btn_row = ctk.CTkFrame(left, fg_color="transparent")
        btn_row.grid(row=4, column=0, sticky="ew", padx=16, pady=(4, 6))
        btn_row.columnconfigure((0, 1), weight=1, uniform="b")
        grey = dict(fg_color=("gray70", "gray28"), hover_color=("gray60", "gray35"),
                    text_color=("black", "white"))
        ctk.CTkButton(btn_row, text="Upload…", command=self.upload_cover, **grey
                      ).grid(row=0, column=0, sticky="ew", padx=(0, 3))
        ctk.CTkButton(btn_row, text="🖼 Grid View…", command=self.open_cover_chooser
                      ).grid(row=0, column=1, sticky="ew", padx=(3, 0))

        ctk.CTkLabel(left, text="Search", font=ctk.CTkFont(weight="bold")
                     ).grid(row=5, column=0, sticky="w", padx=16)
        self.provider = ctk.CTkOptionMenu(left, values=["All"] + list(REGIONS))
        self.provider.grid(row=6, column=0, sticky="ew", padx=16, pady=(2, 3))
        self.s_title = ctk.CTkEntry(left, placeholder_text="Search Title")
        self.s_title.grid(row=7, column=0, sticky="ew", padx=16, pady=3)
        self.s_author = ctk.CTkEntry(left, placeholder_text="Author")
        self.s_author.grid(row=8, column=0, sticky="ew", padx=16, pady=3)
        self.search_btn = ctk.CTkButton(left, text="Search", command=self.search)
        self.search_btn.grid(row=9, column=0, sticky="ew", padx=16, pady=3)
        ctk.CTkLabel(left, text="Matches (best first)", anchor="w",
                     text_color=("gray30", "gray70")
                     ).grid(row=10, column=0, sticky="w", padx=16, pady=(4, 0))
        self.result_menu = ctk.CTkOptionMenu(left, values=["(no results)"],
                                             command=self.on_result_chosen,
                                             dynamic_resizing=False)
        self.result_menu.grid(row=11, column=0, sticky="ew", padx=16, pady=(2, 12))

    def _build_form(self):
        form = ctk.CTkFrame(self, corner_radius=10)
        form.grid(row=1, column=1, sticky="nsew", padx=(7, 14), pady=6)
        for c in range(4):
            form.columnconfigure(c, weight=1, uniform="col")
        self.e = {}

        def field(key, label, row, col, span=1, hint=""):
            ctk.CTkLabel(form, text=label + hint, anchor="w",
                         font=ctk.CTkFont(weight="bold")
                         ).grid(row=row, column=col, columnspan=span, sticky="w",
                                padx=12, pady=(10, 0))
            ent = ctk.CTkEntry(form)
            ent.grid(row=row + 1, column=col, columnspan=span, sticky="ew",
                     padx=12, pady=(2, 0))
            self.e[key] = ent

        field("title", "Title", 0, 0, 3)
        field("year", "Publish Year", 0, 3)
        field("subtitle", "Subtitle", 2, 0, 4)
        field("authors", "Authors", 4, 0, 2, "  (separate with ;)")
        field("narrators", "Narrators", 4, 2, 2, "  (separate with ;)")
        field("series", "Series", 6, 0, 2, "  (separate with ;)")
        field("genres", "Genres", 6, 2, 2, "  (separate with ;)")
        field("tags", "Tags", 8, 0, 2, "  (separate with ;)")
        field("publisher", "Publisher", 8, 2, 1)
        field("language", "Language", 8, 3, 1)
        field("asin", "ASIN", 10, 0, 2)
        field("isbn", "ISBN", 10, 2, 2)

        self.abridged = ctk.CTkCheckBox(form, text="Abridged")
        self.abridged.grid(row=12, column=0, sticky="w", padx=12, pady=(12, 0))
        self.explicit = ctk.CTkCheckBox(form, text="Explicit")
        self.explicit.grid(row=12, column=1, sticky="w", padx=12, pady=(12, 0))

        ctk.CTkLabel(form, text="Description", anchor="w", font=ctk.CTkFont(weight="bold")
                     ).grid(row=13, column=0, sticky="w", padx=12, pady=(10, 0))
        self.desc = ctk.CTkTextbox(form, wrap="word")
        self.desc.grid(row=14, column=0, columnspan=4, sticky="nsew", padx=12, pady=(2, 12))
        form.rowconfigure(14, weight=1)

    def _build_bottom(self):
        bar = ctk.CTkFrame(self, corner_radius=10)
        bar.grid(row=2, column=0, columnspan=2, sticky="ew", padx=14, pady=(6, 14))
        bar.columnconfigure(0, weight=1)

        # row 0 (left of Back/Forward): batch-wide commit, only enabled once the scan is done
        self.commit_all_btn = ctk.CTkButton(bar, text="✔  Commit all good matches", width=220,
                                            state="disabled", command=self.commit_all)
        self.commit_all_btn.grid(row=0, column=0, sticky="e", padx=(0, 6), pady=(10, 0))

        # row 0: Back / Forward, sitting directly above the three action buttons
        self.nav_btns = ctk.CTkFrame(bar, fg_color="transparent")
        self.nav_btns.grid(row=0, column=1, columnspan=3, sticky="ew", padx=(4, 12),
                           pady=(10, 0))
        self.nav_btns.columnconfigure((0, 1), weight=1, uniform="nb")
        self.back_btn = ctk.CTkButton(self.nav_btns, text="◀  Back",
                                      command=lambda: self.go(-1))
        self.back_btn.grid(row=0, column=0, sticky="ew", padx=(0, 3))
        self.fwd_btn = ctk.CTkButton(self.nav_btns, text="Forward  ▶",
                                     command=lambda: self.go(1))
        self.fwd_btn.grid(row=0, column=1, sticky="ew", padx=(3, 0))

        # row 1: status + Re-Scan / Discard / Commit
        self.status = ctk.CTkLabel(bar, text="Select a book folder to begin.", anchor="w")
        self.status.grid(row=1, column=0, sticky="ew", padx=14)
        ctk.CTkButton(bar, text="Re-Scan / Search", width=140,
                      fg_color=("gray70", "gray28"), hover_color=("gray60", "gray35"),
                      text_color=("black", "white"),
                      command=self.search).grid(row=1, column=1, padx=4, pady=(6, 10))
        ctk.CTkButton(bar, text="Discard", width=110, fg_color="#a33", hover_color="#822",
                      command=self.discard).grid(row=1, column=2, padx=4, pady=(6, 10))
        self.commit_btn = ctk.CTkButton(bar, text="Commit & Save Files", width=200, height=40,
                                        font=ctk.CTkFont(size=15, weight="bold"),
                                        fg_color="#2e8b3d", hover_color="#236b2f",
                                        command=self.commit)
        self.commit_btn.grid(row=1, column=3, padx=(4, 12), pady=(6, 10))

    # ------------------------------- Utilities ------------------------------- #
    def set_status(self, msg):
        self.status.configure(text=msg)

    def set_entry(self, key, value):
        ent = self.e[key]
        ent.delete(0, "end")
        ent.insert(0, value or "")

    def _set_cover_image(self, ci, text):
        """Swap the cover image safely. The previous CTkImage stays referenced (deque)
        so Tk never ends up pointing at a deleted image - that was the root cause of
        the 'stuck after two books' bug."""
        self._cover_refs.append(ci)
        self.cover_label.configure(text=text, image=ci)

    def show_cover(self, data, source=""):
        """Display image bytes as the cover. Returns False if the bytes aren't an image."""
        try:
            img = Image.open(io.BytesIO(data))
            img.load()
        except Exception:
            return False
        self.cover_bytes = data
        label = f"{img.width}×{img.height}px" + (f"  ·  {source}" if source else "")
        self.res_label.configure(text=label)
        thumb = img.convert("RGB")
        thumb.thumbnail((COVER_PX, COVER_PX))
        ci = ctk.CTkImage(light_image=thumb, dark_image=thumb, size=thumb.size)
        self._set_cover_image(ci, "")
        return True

    def clear_cover(self, note=""):
        self.cover_bytes = None
        self.res_label.configure(text=note)
        self._set_cover_image(self.placeholder_img, "No cover")

    def clear_form(self):
        for k in self.e:
            self.set_entry(k, "")
        self.abridged.deselect()
        self.explicit.deselect()
        self.desc.delete("1.0", "end")
        self._published_date = ""

    def reset_results(self):
        self.results = []
        self.result_labels = ["(no results)"]
        self.result_menu.configure(values=self.result_labels)
        self.result_menu.set("(no results)")

    def set_search_fields(self, title, author):
        self.s_title.delete(0, "end")
        self.s_title.insert(0, title)
        self.s_author.delete(0, "end")
        self.s_author.insert(0, author)

    # ------------------------- Per-book state (batch) ------------------------ #
    def snapshot(self):
        return {
            "fields": {k: self.e[k].get() for k in self.e},
            "abridged": bool(self.abridged.get()),
            "explicit": bool(self.explicit.get()),
            "desc": self.desc.get("1.0", "end-1c"),
            "cover": self.cover_bytes,
            "res_text": self.res_label.cget("text"),
            "results": self.results,
            "labels": self.result_labels,
            "sel": self.result_menu.get(),
            "s_title": self.s_title.get(),
            "s_author": self.s_author.get(),
            "provider": self.provider.get(),
            "date": self._published_date,
        }

    def restore(self, s):
        self.reset_cover_nav()
        for k, v in s["fields"].items():
            self.set_entry(k, v)
        (self.abridged.select if s["abridged"] else self.abridged.deselect)()
        (self.explicit.select if s["explicit"] else self.explicit.deselect)()
        self.desc.delete("1.0", "end")
        self.desc.insert("1.0", s["desc"])
        self.results = s["results"]
        self.result_labels = s["labels"]
        self.result_menu.configure(values=self.result_labels)
        self.result_menu.set(s["sel"])
        self.set_search_fields(s["s_title"], s["s_author"])
        self.provider.set(s["provider"])
        self._published_date = s["date"]
        if s["cover"] and self.show_cover(s["cover"]):
            self.res_label.configure(text=s.get("res_text", ""))
        else:
            self.clear_cover(s.get("res_text", ""))

    # ------------------------------ Prefetching ------------------------------ #
    def stop_prefetch(self):
        self.batch_id += 1
        if self.executor:
            self.executor.shutdown(wait=False, cancel_futures=True)
            self.executor = None
        self.prefetch, self.pf_pending, self.conf = {}, set(), {}
        self.pf_total = 0
        self.pf_summary = ""
        self.waiting_key = None
        self.pf_label.configure(text="")
        self.pf_bar.set(0)

    def start_prefetch(self, books):
        """Search Audible (and warm the cover cache) for EVERY folder, in the background."""
        self.stop_prefetch()
        bid = self.batch_id
        sel = self.provider.get()
        regions = list(REGIONS) if sel == "All" else [sel]
        self.pf_pending = {str(b) for b in books}
        self.pf_total = len(books)
        self.pf_label.configure(text=f"Searching 0/{self.pf_total}")
        self.pf_bar.set(0)
        self.executor = ThreadPoolExecutor(max_workers=PREFETCH_WORKERS)
        for b in books:
            self.executor.submit(self._pf_task, bid, b, regions)
        self.refresh_batch_buttons()

    def _pf_task(self, bid, folder, regions):
        if bid != self.batch_id:
            return
        key = str(folder)
        try:
            results, errors = smart_search(regions, folder.name, folder.parent.name,
                                           folder=folder)
        except Exception as ex:
            log_error(f"search failed for {folder}: {ex}")
            results, errors = [], [str(ex)]
        if results and bid == self.batch_id:      # warm the disk cache for instant covers
            try:
                t, a = prefill_fields(folder)
                resolve_cover(results[0], results[1:5], t, a)
            except Exception as ex:
                log_error(f"cover prefetch failed for {folder}: {ex}")
        data = {"results": results, "errors": errors}
        self.post(lambda: self._pf_done(bid, key, data))

    def _pf_done(self, bid, key, data):
        if bid != self.batch_id:
            return
        self.pf_pending.discard(key)
        self.prefetch[key] = data
        best = data["results"][0]["score"] if data["results"] else 0.0
        self.conf.setdefault(key, best)
        done = self.pf_total - len(self.pf_pending)
        self.pf_bar.set(done / max(1, self.pf_total))
        if self.pf_pending:
            self.pf_label.configure(text=f"Searching {done}/{self.pf_total}")
        else:
            self.pf_summary = self.scan_summary()
            self.pf_label.configure(text=self.pf_summary)
            self.refresh_batch_buttons()
        if self.waiting_key == key and self.book_dir and str(self.book_dir) == key:
            self.waiting_key = None
            self.show_results(data["results"], data["errors"])
        self.update_nav()

    # ------------------------------- Mode / nav ------------------------------ #
    def set_mode(self, mode):
        if self.busy:
            self.mode_btn.set(self.mode)
            self.set_status("Please wait - a batch operation is running.")
            return
        self.mode = mode
        self.mode_btn.set(mode)
        self.gen += 1
        self.reset_cover_nav()
        self.stop_prefetch()
        self.book_dir = None
        self.all_books, self.books, self.index = [], [], -1
        self.cache.clear()
        self.existing_meta, self.existing_cover_bytes = {}, None
        self.clear_form()
        self.clear_cover()
        self.reset_results()
        self.set_search_fields("", "")
        self.path_label.configure(text="No folder selected")
        if mode == MODE_BATCH:
            self.pick_btn.configure(text="📚  Select Library Folder")
            self.nav.grid()
            self.nav_btns.grid()
            self.commit_all_btn.grid()
            self.update_nav()
            self.set_status("Batch mode: select your library root (e.g. E:\\Audiobooks).")
        elif mode == MODE_EDIT:
            self.pick_btn.configure(text="📂  Open Existing Folder")
            self.nav.grid_remove()
            self.nav_btns.grid_remove()
            self.commit_all_btn.grid_remove()
            self.set_status("Open a folder that already contains metadata.json "
                            "(and cover.jpg) to edit it.")
        else:
            self.pick_btn.configure(text="📁  Select Book Folder")
            self.nav.grid_remove()
            self.nav_btns.grid_remove()
            self.commit_all_btn.grid_remove()
            self.set_status("Select a book folder to begin.")
        self.refresh_batch_buttons()

    def update_nav(self):
        n = len(self.books)
        if n == 0 or self.index < 0 or self.book_dir is None:
            self.counter.configure(text="No books loaded")
            self.back_btn.configure(state="disabled")
            self.fwd_btn.configure(state="disabled")
            return
        key = str(self.book_dir)
        flags = ""
        if key in self.committed:
            flags += "   ✔ saved"
        c = self.conf.get(key)
        if c is None:
            if key in self.pf_pending:
                flags += "   ⏳ searching…"
        elif c == 0:
            flags += "   ✖ no match"
        elif c < CHECK_SCORE:
            flags += f"   ⚠ {int(c * 100)}% match"
        elif c < GOOD_SCORE:
            flags += f"   ? {int(c * 100)}% match"
        else:
            flags += f"   ● {int(c * 100)}% match"
        rel = self.book_dir.parent.name + "  ›  " + self.book_dir.name
        self.counter.configure(text=f"Book {self.index + 1} of {n}   |   {rel}{flags}")
        self.back_btn.configure(state="normal" if self.index > 0 else "disabled")
        self.fwd_btn.configure(state="normal" if self.index < n - 1 else "disabled")

    def go(self, delta):
        if self.busy or self.mode != MODE_BATCH or not self.books:
            return
        new = self.index + delta
        if 0 <= new < len(self.books):
            self.load_book(new)

    def load_book(self, index):
        # remember what's on screen for the book we're leaving
        try:
            if (self.book_dir is not None and self.index >= 0
                    and self.waiting_key != str(self.book_dir)):
                self.cache[str(self.book_dir)] = self.snapshot()
        except Exception:
            log_error("snapshot failed:\n" + traceback.format_exc())
        self.gen += 1
        self.reset_cover_nav()
        self.waiting_key = None
        self.index = index
        self.book_dir = self.books[index]
        key = str(self.book_dir)
        self.path_label.configure(text=key)
        self.update_nav()
        try:
            self._populate_book(key)
        except Exception as ex:
            self._report(f"load_book failed for {key}\n" + traceback.format_exc(),
                         str(ex)[:120])

    def _populate_book(self, key):
        snap = self.cache.get(key)
        if snap:
            self.restore(snap)
            self.set_status("Restored your earlier review of this book.")
            return
        self.clear_form()
        self.clear_cover()
        self.reset_results()
        self.set_search_fields(*prefill_fields(self.book_dir))
        data = self.prefetch.get(key)
        if data is not None:
            self.show_results(data["results"], data["errors"])
        elif key in self.pf_pending:
            self.waiting_key = key
            self.set_status("Searching Audible… (queued in background)")
        else:
            self.search()

    def refilter(self):
        if self.mode != MODE_BATCH or not self.all_books:
            return
        current = self.book_dir
        if self.hide_done.get():
            self.books = [b for b in self.all_books
                          if not (b / "metadata.json").exists() or b == current]
        else:
            self.books = list(self.all_books)
        if not self.books:
            self.index, self.book_dir = -1, None
            self.clear_form()
            self.clear_cover()
            self.reset_results()
            self.update_nav()
            self.set_status("Every book already has metadata.json.")
            return
        if current in self.books:
            self.index = self.books.index(current)
            self.update_nav()
        else:
            self.book_dir = None
            self.load_book(0)

    # -------------------------------- Actions -------------------------------- #
    def pick_folder(self):
        if self.busy:
            self.set_status("Please wait - a batch operation is running.")
            return
        key = "last_root" if self.mode == MODE_BATCH else "last_dir"
        start = self.cfg.get(key) or "E:\\Audiobooks"
        title = ("Select library root folder" if self.mode == MODE_BATCH
                 else "Select an already-populated audiobook folder"
                 if self.mode == MODE_EDIT else "Select audiobook folder")
        path = filedialog.askdirectory(title=title,
                                       initialdir=start if os.path.isdir(start) else None)
        if not path:
            return
        p = Path(path)

        if self.mode == MODE_EDIT:
            self.cfg["last_dir"] = str(p.parent)
            save_config(self.cfg)
            self.load_existing(p)
            return

        if self.mode == MODE_BATCH:
            self.cfg["last_root"] = str(p)
            save_config(self.cfg)
            self.set_status("Scanning for Author › Title › File(s) folders…")
            self.update_idletasks()
            found = scan_library(p)
            if not found:
                messagebox.showinfo(
                    APP_NAME,
                    "No audiobooks found.\n\nExpected layout:\n"
                    "  <selected folder>\\Author\\Title\\audio files")
                self.set_status("No audiobooks found in that folder.")
                return
            self.gen += 1
            self.all_books = found
            self.books = ([b for b in found if not (b / "metadata.json").exists()]
                          if self.hide_done.get() else list(found))
            self.cache.clear()
            self.committed.clear()
            self.book_dir, self.index = None, -1
            self.path_label.configure(text=str(p))
            self.start_prefetch(found)          # search ALL folders in the background
            if not self.books:
                self.clear_form()
                self.clear_cover()
                self.reset_results()
                self.update_nav()
                self.set_status("Every book already has metadata.json.")
                return
            self.load_book(0)
            self.set_status(f"Found {len(found)} audiobook(s); searching them all in the "
                            f"background. Review each, then Commit individually.")
            return

        # single mode
        self.book_dir = p
        self.cfg["last_dir"] = str(p.parent)
        save_config(self.cfg)
        self.gen += 1
        self.path_label.configure(text=str(p))
        self.clear_form()
        self.clear_cover()
        self.reset_results()
        self.set_search_fields(*prefill_fields(p))
        self.search()

    def search(self):
        """Manual / single-mode search using whatever is typed in the Search boxes."""
        title = self.s_title.get().strip()
        author = self.s_author.get().strip()
        if not title and not author:
            messagebox.showinfo(APP_NAME, "Enter a title or author to search.")
            return
        sel = self.provider.get()
        regions = list(REGIONS) if sel == "All" else [sel]
        self.gen += 1
        gen = self.gen
        self.waiting_key = None
        folder = self.book_dir
        if folder is not None:
            self.skipped.discard(str(folder))             # user is actively re-reviewing it
        self.search_btn.configure(state="disabled")
        self.set_status("Searching Audible…")
        threading.Thread(target=self._search_worker,
                         args=(gen, regions, title, author, folder), daemon=True).start()

    def _search_worker(self, gen, regions, title, author, folder):
        try:
            results, errors = smart_search(regions, title, author, folder=folder, exact=True)
        except Exception as ex:
            log_error(f"manual search failed: {ex}")
            results, errors = [], [str(ex)]
        self.post(lambda: self._search_done(gen, results, errors))

    def _search_done(self, gen, results, errors):
        self.search_btn.configure(state="normal")
        if gen != self.gen:       # user moved on to another book / search
            return
        self.show_results(results, errors)

    def show_results(self, results, errors):
        """Populate the results menu + form from a (sorted) list of matches."""
        self.results = results
        key = str(self.book_dir) if self.book_dir else None
        if not results:
            self.result_labels = ["(no results)"]
            self.result_menu.configure(values=self.result_labels)
            self.result_menu.set("(no results)")
            if key:
                self.conf[key] = 0.0
            msg = "No matches found - edit the search fields and click Search."
            if errors:
                msg += "  " + " | ".join(errors)
            self.set_status(msg)
            self.update_nav()
            return
        labels = []
        for i, r in enumerate(results):
            tag = "UK" if r["region"].endswith("uk") else "US"
            lab = (f"{i + 1}. [{tag}] {int(r['score'] * 100)}%  {r['title']} — "
                   f"{', '.join(r['authors'])} ({r['year']})")
            labels.append(lab[:74])
        self.result_labels = [l if labels.count(l) == 1 else f"{l} #{i}"
                              for i, l in enumerate(labels)]
        self.result_menu.configure(values=self.result_labels)
        self.result_menu.set(self.result_labels[0])
        self.apply_result(results[0])
        best = results[0]["score"]
        if key:
            self.conf[key] = best
        if best >= GOOD_SCORE:
            quality = f"Good match ({int(best * 100)}%)."
        elif best >= CHECK_SCORE:
            quality = f"Possible match ({int(best * 100)}%) - please verify."
        else:
            quality = f"⚠ Low-confidence ({int(best * 100)}%) - check carefully or edit the search."
        note = ""
        if self.book_dir and (self.book_dir / "metadata.json").exists():
            note = "  (folder already has a metadata.json)"
        self.set_status(f"{len(results)} result(s). {quality}{note}"
                        + (f"  ({' | '.join(errors)})" if errors else ""))
        self.update_nav()

    def on_result_chosen(self, label):
        if label in self.result_labels and self.results:
            self.apply_result(self.results[self.result_labels.index(label)])

    def apply_result(self, r):
        self.set_entry("title", r["title"])
        self.set_entry("subtitle", r["subtitle"])
        self.set_entry("authors", join_list(r["authors"]))
        self.set_entry("narrators", join_list(r["narrators"]))
        self.set_entry("series", join_list(r["series"]))
        self.set_entry("genres", join_list(r["genres"]))
        self.set_entry("tags", "")
        self.set_entry("year", r["year"])
        self.set_entry("publisher", r["publisher"])
        self.set_entry("language", r["language"])
        self.set_entry("asin", r["asin"])
        self.set_entry("isbn", r["isbn"])
        (self.abridged.select if r["abridged"] else self.abridged.deselect)()
        (self.explicit.select if r["explicit"] else self.explicit.deselect)()
        self.desc.delete("1.0", "end")
        self.desc.insert("1.0", r["description"])
        self._published_date = r["date"]

        # cover: never leave a previous book's cover on screen
        self.clear_cover("Loading cover…")
        self.reset_cover_nav()
        gen = self.cgen
        fallbacks = [x for x in self.results if x is not r][:4]
        title = self.s_title.get().strip() or r["title"]
        author = self.s_author.get().strip() or (r["authors"][0] if r["authors"] else "")
        threading.Thread(target=self._cover_worker,
                         args=(gen, r, fallbacks, title, author), daemon=True).start()

    def _cover_worker(self, gen, item, fallbacks, title, author):
        try:
            data, size, src = resolve_cover(item, fallbacks, title, author)
        except Exception as ex:
            msg = str(ex)
            log_error(f"cover failed for '{item.get('title')}': {msg}")
            self.post(lambda: self._cover_failed(gen))
            return
        self.post(lambda: self._cover_ready(gen, data, src))

    def _cover_ready(self, gen, data, src):
        if gen != self.cgen:
            return
        if not self.show_cover(data, src):
            self._cover_failed(gen)

    def _cover_failed(self, gen):
        if gen != self.cgen:
            return
        self.clear_cover("⚠ No cover found - try Find Covers…")

    # ----------------------- Large cover preview (click cover) ----------------------- #
    def open_cover_preview(self, event=None):
        if not self.cover_bytes:
            return
        try:
            img = Image.open(io.BytesIO(self.cover_bytes))
            img.load()
        except Exception:
            return
        try:
            if self._preview_win is not None and self._preview_win.winfo_exists():
                self._preview_win.destroy()
        except Exception:
            pass
        w, h = img.size
        try:
            scaling = float(self._get_window_scaling())
        except Exception:
            scaling = 1.0
        limit = int(min(self.winfo_screenwidth(), self.winfo_screenheight()) * 0.80 / scaling)
        k = min(1.0, limit / max(w, h))              # shrink to fit the screen, never enlarge
        disp = img.convert("RGB").resize((max(1, int(w * k)), max(1, int(h * k))),
                                         Image.LANCZOS)
        src = self.res_label.cget("text").split("·")[-1].strip()
        win = ctk.CTkToplevel(self)
        win.title(f"Cover preview - {w}×{h}px")
        ci = ctk.CTkImage(light_image=disp, dark_image=disp, size=disp.size)
        win._ref = ci
        lbl = ctk.CTkLabel(win, image=ci, text="", cursor="hand2")
        lbl.pack(padx=12, pady=(12, 4))
        cap = f"{w}×{h}px" + (f"  ·  {src}" if src and "px" not in src else "")
        ctk.CTkLabel(win, text=f"{cap}      (click the image or press Esc to close)",
                     text_color=("gray30", "gray70")).pack(pady=(0, 10))
        close = lambda e=None: win.destroy()
        lbl.bind("<Button-1>", close)
        win.bind("<Escape>", close)
        win.update_idletasks()
        x = max(0, (self.winfo_screenwidth() - win.winfo_reqwidth()) // 2)
        y = max(0, (self.winfo_screenheight() - win.winfo_reqheight()) // 3)
        win.geometry(f"+{x}+{y}")
        win.after(150, win.lift)
        win.after(200, win.focus_force)
        self._preview_win = win

    # -------------------- Open Existing: edit a populated folder -------------------- #
    @staticmethod
    def _as_list(v):
        if v is None:
            return []
        if isinstance(v, (list, tuple)):
            out = []
            for x in v:
                if isinstance(x, dict):                      # {"name": ..., "sequence": ...}
                    n = str(x.get("name") or x.get("title") or "").strip()
                    seq = x.get("sequence")
                    x = f"{n} #{seq}" if n and seq else n
                x = str(x).strip()
                if x:
                    out.append(x)
            return out
        v = str(v).strip()
        return [v] if v else []

    def load_existing(self, folder):
        """Load metadata.json + cover from an already-populated folder for editing."""
        self.gen += 1
        self.reset_cover_nav()
        meta_path = folder / "metadata.json"
        if not meta_path.is_file():
            if not messagebox.askyesno(
                    APP_NAME, "No metadata.json was found in this folder.\n\n"
                              "Search Audible for it instead?"):
                return False
            self.book_dir = folder
            self.existing_meta, self.existing_cover_bytes = {}, None
            self.path_label.configure(text=str(folder))
            self.clear_form()
            self.clear_cover()
            self.reset_results()
            self.set_search_fields(*prefill_fields(folder))
            self.search()
            return True
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8-sig"))
            if not isinstance(meta, dict):
                raise ValueError("metadata.json is not a JSON object")
        except Exception as ex:
            messagebox.showerror(APP_NAME, f"Could not read metadata.json:\n{ex}")
            return False

        self.book_dir = folder
        self.existing_meta = meta
        self.existing_cover_bytes = None
        self.path_label.configure(text=str(folder))
        self.clear_form()
        self.reset_results()
        L = self._as_list
        self.set_entry("title", str(meta.get("title") or ""))
        self.set_entry("subtitle", str(meta.get("subtitle") or ""))
        self.set_entry("authors", join_list(L(meta.get("authors"))))
        self.set_entry("narrators", join_list(L(meta.get("narrators"))))
        self.set_entry("series", join_list(L(meta.get("series"))))
        self.set_entry("genres", join_list(L(meta.get("genres"))))
        self.set_entry("tags", join_list(L(meta.get("tags"))))
        self.set_entry("year", str(meta.get("publishedYear") or ""))
        self.set_entry("publisher", str(meta.get("publisher") or ""))
        self.set_entry("language", str(meta.get("language") or ""))
        self.set_entry("asin", str(meta.get("asin") or ""))
        self.set_entry("isbn", str(meta.get("isbn") or ""))
        (self.abridged.select if meta.get("abridged") else self.abridged.deselect)()
        (self.explicit.select if meta.get("explicit") else self.explicit.deselect)()
        self.desc.insert("1.0", str(meta.get("description") or ""))
        self._published_date = str(meta.get("publishedDate") or "")

        shown = ""
        for name in COVER_NAMES:
            cp = folder / name
            if cp.is_file():
                try:
                    data = cp.read_bytes()
                except Exception:
                    continue
                if self.show_cover(data, f"existing {name}"):
                    self.existing_cover_bytes = data
                    shown = name
                    break
        if not shown:
            self.clear_cover("No cover file in this folder")
        authors = L(meta.get("authors"))
        self.set_search_fields(str(meta.get("title") or folder.name),
                               authors[0] if authors else "")
        self.set_status("Loaded the existing metadata.json - edit anything, then Commit & "
                        "Save Files. (Search / ◀ ▶ will fetch alternatives from Audible.)")
        return True

    # --------------- Batch: "Commit all good matches" and "Move Matched" --------------- #
    def scan_summary(self):
        vals = [self.conf.get(str(b), 0) for b in self.all_books]
        good = sum(v >= GOOD_SCORE for v in vals)
        none = sum(v == 0 for v in vals)
        return f"Done: {good} good · {len(vals) - good - none} to check · {none} no match"

    @staticmethod
    def _style_btn(btn, enabled, color, hover):
        btn.configure(state="normal" if enabled else "disabled",
                      fg_color=color if enabled else ("gray65", "gray30"),
                      hover_color=hover if enabled else ("gray65", "gray30"))

    def refresh_batch_buttons(self):
        """Both buttons stay greyed out until the whole batch scan has finished."""
        complete = (self.mode == MODE_BATCH and self.pf_total > 0
                    and not self.pf_pending and not self.busy)
        self.matched_count = (sum(1 for b in self.all_books if is_committed(b))
                              if complete else 0)
        self._style_btn(self.commit_all_btn, complete, "#17806d", "#116655")
        self._style_btn(self.move_btn, complete and self.matched_count > 0,
                        "#9a6b1f", "#7a5416")

    def set_busy(self, flag):
        self.busy = flag
        if flag:
            for b in (self.back_btn, self.fwd_btn, self.commit_btn):
                b.configure(state="disabled")
        else:
            self.commit_btn.configure(state="normal")
            self.update_nav()
        self.refresh_batch_buttons()

    def _progress(self, label, i, n):
        self.pf_label.configure(text=f"{label} {i}/{n}")
        self.pf_bar.set(i / max(1, n))

    @staticmethod
    def _rel(folder):
        return f"{folder.parent.name}\\{folder.name}"

    # ---- Commit all good matches ----
    def plan_commit_all(self):
        """Decide which books qualify. Returns (jobs, stats)."""
        jobs = []
        st = {"existing": 0, "low": 0, "discarded": 0, "none": 0}
        cur_key = str(self.book_dir) if self.book_dir else None
        for b in self.all_books:
            key = str(b)
            need_meta = not (b / "metadata.json").is_file()
            need_cover = not has_cover(b)
            if not need_meta and not need_cover:
                st["existing"] += 1                     # already has JSON + cover
                continue
            if key in self.skipped:
                st["discarded"] += 1
                continue
            if self.conf.get(key, 0) < GOOD_SCORE:
                st["none" if self.conf.get(key, 0) == 0 else "low"] += 1
                continue
            # what to write: the user's reviewed/edited state if they've seen the book,
            # otherwise the top Audible match
            snap = self.snapshot() if key == cur_key else self.cache.get(key)
            job = {"folder": b, "need_meta": need_meta, "need_cover": need_cover}
            if snap and snap["fields"]["title"].strip():
                results = snap["results"] or []
                idx = (snap["labels"].index(snap["sel"])
                       if snap["sel"] in snap["labels"] else 0)
                item = results[idx] if idx < len(results) else (results[0] if results else None)
                job.update(fields=snap["fields"], abridged=snap["abridged"],
                           explicit=snap["explicit"], desc=snap["desc"], date=snap["date"],
                           cover=snap["cover"], title=snap["s_title"], author=snap["s_author"])
            else:
                data = self.prefetch.get(key)
                results = data["results"] if data else []
                if not results:
                    st["none"] += 1
                    continue
                item = results[0]
                t, a = prefill_fields(b)
                job.update(fields=fields_from_item(item), abridged=item["abridged"],
                           explicit=item["explicit"], desc=item["description"],
                           date=item["date"], cover=None, title=t, author=a)
            if item is None and need_cover and not job["cover"]:
                st["none"] += 1                         # nothing to fetch a cover from
                continue
            job["item"] = item
            job["fallbacks"] = [r for r in results if r is not item][:4]
            jobs.append(job)
        return jobs, st

    @staticmethod
    def _skip_text(st):
        pct = int(GOOD_SCORE * 100)
        parts = []
        if st["existing"]:
            parts.append(f"{st['existing']} already have a JSON + cover")
        if st["low"]:
            parts.append(f"{st['low']} are below a {pct}% match")
        if st["none"]:
            parts.append(f"{st['none']} have no usable match")
        if st["discarded"]:
            parts.append(f"{st['discarded']} were discarded by you")
        return ("Skipped: " + "; ".join(parts) + ".") if parts else ""

    def commit_all(self):
        if self.busy or self.mode != MODE_BATCH:
            return
        jobs, st = self.plan_commit_all()
        skip = self._skip_text(st)
        pct = int(GOOD_SCORE * 100)
        if not jobs:
            messagebox.showinfo(APP_NAME, "Nothing to commit.\n\n" + skip)
            return
        if not messagebox.askyesno(
                APP_NAME, f"Commit {len(jobs)} good match(es) (≥ {pct}%)?\n\n"
                          "This writes cover.jpg and metadata.json into each folder. "
                          "Existing files are never overwritten.\n\n" + skip + "\n\nContinue?"):
            return
        self.set_busy(True)
        self.set_status(f"Committing {len(jobs)} book(s)…")
        threading.Thread(target=self._commit_all_worker, args=(jobs,), daemon=True).start()

    def _commit_all_worker(self, jobs):
        ok, failed, n = [], [], len(jobs)
        for i, job in enumerate(jobs, 1):
            try:
                write_job(job)
                ok.append(job["folder"])
            except Exception as ex:
                log_error(f"commit-all failed for {job['folder']}: {ex}")
                failed.append((job["folder"], str(ex)))
            self.post(lambda i=i: self._progress("Committing", i, n))
        self.post(lambda: self._commit_all_done(ok, failed))

    def _commit_all_done(self, ok, failed):
        self.committed.update(str(f) for f in ok)
        self.set_busy(False)
        self.pf_label.configure(text=self.scan_summary())
        lines = [f"Committed {len(ok)} book(s)."]
        if failed:
            lines.append(f"\n{len(failed)} could not be committed (nothing was written for them):")
            lines += [f"  • {self._rel(f)} - {why[:80]}" for f, why in failed[:8]]
            if len(failed) > 8:
                lines.append(f"  …and {len(failed) - 8} more (see error.log)")
        self.set_status(f"Commit all finished: {len(ok)} committed"
                        + (f", {len(failed)} failed" if failed else "") + ".")
        messagebox.showinfo(APP_NAME, "\n".join(lines))

    # ---- Move Matched ----
    @staticmethod
    def _inside(child: Path, parent: Path):
        try:
            child.resolve().relative_to(parent.resolve())
            return True
        except Exception:
            return False

    def move_matched(self):
        if self.busy or self.mode != MODE_BATCH:
            return
        matched = [b for b in self.all_books if is_committed(b)]
        if not matched:
            messagebox.showinfo(APP_NAME, "No book folders with both a metadata.json and a "
                                          "cover file were found.")
            return
        start = self.cfg.get("last_move_dest")
        dest = filedialog.askdirectory(
            title="Move matched books to…",
            initialdir=start if start and os.path.isdir(start) else None)
        if not dest:
            return
        dest = Path(dest)
        self.cfg["last_move_dest"] = str(dest)
        save_config(self.cfg)

        plan, problems = [], []
        for b in matched:
            target = dest / b.parent.name / b.name            # keep Author\Book
            try:
                if target.resolve() == b.resolve():
                    continue                                  # already there
            except Exception:
                pass
            if self._inside(dest, b):
                problems.append((b, "destination is inside this book's folder"))
            elif target.exists():
                problems.append((b, "already exists at the destination"))
            else:
                plan.append((b, target))
        if not plan:
            messagebox.showinfo(APP_NAME, "Nothing to move.\n\n" + "\n".join(
                f"  • {self._rel(b)} - {why}" for b, why in problems[:8]))
            return
        note = (f"\n\n{len(problems)} will be skipped (already exist at the destination)."
                if problems else "")
        if not messagebox.askyesno(
                APP_NAME, f"Move {len(plan)} finished book folder(s) to:\n{dest}\n\n"
                          f"Each is moved as Author\\Book (the author folder is recreated "
                          f"there).{note}\n\nContinue?"):
            return
        self.set_busy(True)
        self.set_status(f"Moving {len(plan)} book folder(s)…")
        threading.Thread(target=self._move_worker, args=(plan, problems, dest),
                         daemon=True).start()

    def _move_worker(self, plan, problems, dest):
        moved, failed, n = [], [], len(plan)
        for i, (src, target) in enumerate(plan, 1):
            try:
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(src), str(target))
                moved.append((src, target))
            except Exception as ex:
                log_error(f"move failed {src} -> {target}: {ex}")
                failed.append((src, str(ex)))
            self.post(lambda i=i: self._progress("Moving", i, n))
        for src, _t in moved:                                 # tidy up emptied author folders
            try:
                src.parent.rmdir()
            except OSError:
                pass
        self.post(lambda: self._move_done(moved, failed, problems, dest))

    def _move_done(self, moved, failed, problems, dest):
        keys = {str(src) for src, _t in moved}
        cur = self.book_dir
        cur_moved = cur is not None and str(cur) in keys
        self.all_books = [b for b in self.all_books if str(b) not in keys]
        self.books = [b for b in self.books if str(b) not in keys]
        for d in (self.cache, self.prefetch, self.conf):
            for k in keys:
                d.pop(k, None)
        self.committed -= keys
        self.skipped -= keys
        self.pf_total = len(self.all_books)
        if cur_moved:
            idx = min(max(self.index, 0), len(self.books) - 1)
            self.book_dir, self.index, self.waiting_key = None, -1, None
            self.gen += 1
            if self.books:
                self.load_book(idx)
            else:
                self.clear_form()
                self.clear_cover()
                self.reset_results()
                self.path_label.configure(text="All books were moved")
        elif cur is not None and cur in self.books:
            self.index = self.books.index(cur)
        self.set_busy(False)
        self.pf_label.configure(text=self.scan_summary())
        lines = [f"Moved {len(moved)} book folder(s) to:\n{dest}"]
        bad = failed + problems
        if bad:
            lines.append(f"\n{len(bad)} not moved:")
            lines += [f"  • {self._rel(f)} - {why[:80]}" for f, why in bad[:8]]
        self.set_status(f"Moved {len(moved)} book folder(s) to {dest}"
                        + (f"  ({len(bad)} not moved)" if bad else ""))
        messagebox.showinfo(APP_NAME, "\n".join(lines))

    # ------------------- Browse covers with the ◀ ▶ arrows ------------------- #
    def reset_cover_nav(self):
        """New book / new result / discard: forget any cover candidates."""
        self.cgen += 1
        self.cover_ctx += 1
        self.cc = {"state": "idle", "cands": [], "pos": 0, "hashes": set(), "pending": 1}
        try:
            self.cover_nav_label.configure(text="Browse more covers")
        except Exception:
            pass

    def cover_step(self, delta):
        """◀ / ▶ clicked. The first click searches for candidates (once per book);
        every later click just moves along the list, downloading only what it shows."""
        cc = self.cc
        if cc["state"] == "loading":
            return
        if cc["state"] == "ready":
            self._goto_cover(cc["pos"] + delta, delta)
            return
        title = self.s_title.get().strip() or self.e["title"].get().strip()
        author = self.s_author.get().strip()
        if not title:
            messagebox.showinfo(APP_NAME, "Search for a book first.")
            return
        cc["state"] = "loading"
        cc["pending"] = delta
        self.cover_nav_label.configure(text="Searching for covers…")
        threading.Thread(target=self._cands_worker,
                         args=(self.cover_ctx, list(self.results), title, author),
                         daemon=True).start()

    def _cands_worker(self, ctx, results, title, author):
        try:
            cands = collect_cover_candidates(results, title, author, broad=True)
        except Exception as ex:
            log_error(f"cover candidate search failed: {ex}")
            cands = []
        self.post(lambda: self._cands_ready(ctx, cands))

    def _cands_ready(self, ctx, cands):
        if ctx != self.cover_ctx:
            return
        cc = self.cc
        items = []
        if self.cover_bytes:               # the cover already on screen is entry #1
            src = self.res_label.cget("text").split("·")[-1].strip() or "Current cover"
            cc["hashes"].add(hashlib.sha1(self.cover_bytes).hexdigest())
            items.append({"label": f"{src} (current)", "urls": [], "data": self.cover_bytes})
        items += [dict(c, data=None) for c in cands]
        cc["cands"] = items
        cc["state"] = "ready"
        if len(items) <= 1:
            self.cover_nav_label.configure(text="No other covers found")
            return
        delta = cc.get("pending", 1)
        start = 0 if self.cover_bytes else (0 if delta > 0 else -1)
        self._goto_cover(start + (delta if self.cover_bytes else 0), delta)

    def _goto_cover(self, pos, direction):
        cc = self.cc
        cands = cc["cands"]
        if not cands:
            cc["state"] = "ready"
            self.cover_nav_label.configure(text="No covers found")
            return
        pos %= len(cands)
        cc["pos"] = pos
        e = cands[pos]
        if e["data"] is not None:
            if self.show_cover(e["data"], e["label"].replace(" (current)", "")):
                self.cgen += 1             # the user's pick beats any in-flight auto cover
                cc["state"] = "ready"
                self.cover_nav_label.configure(text=f"Cover {pos + 1} of {len(cands)}")
                self._warm_neighbour(pos, direction)
                return
            self._drop_candidate(pos, direction)
            self._goto_cover(cc["pos"], direction)
            return
        cc["state"] = "loading"
        self.cover_nav_label.configure(text="Loading cover…")
        threading.Thread(target=self._fetch_cand_worker,
                         args=(self.cover_ctx, e, direction), daemon=True).start()

    def _fetch_cand_worker(self, ctx, e, direction):
        try:
            data, size = fetch_first_good(e["urls"], first_wins=e.get("first_wins", False))
        except Exception as ex:
            log_error(f"cover candidate failed ({e['label']}): {ex}")
            data = None
        self.post(lambda: self._cand_fetched(ctx, e, data, direction))

    def _cand_fetched(self, ctx, e, data, direction):
        if ctx != self.cover_ctx:
            return
        cc = self.cc
        try:
            idx = next(i for i, c in enumerate(cc["cands"]) if c is e)
        except StopIteration:
            return
        if data is not None:
            h = hashlib.sha1(data).hexdigest()
            if h in cc["hashes"]:          # same picture as one we already have
                data = None
            else:
                cc["hashes"].add(h)
                e["data"] = data
        if data is None:                   # failed or duplicate: skip it
            self._drop_candidate(idx, direction)
            self._goto_cover(cc["pos"], direction)
            return
        self._goto_cover(idx, direction)

    def _drop_candidate(self, idx, direction):
        cc = self.cc
        del cc["cands"][idx]
        if cc["cands"]:
            cc["pos"] = (idx if direction > 0 else idx - 1) % len(cc["cands"])

    def _warm_neighbour(self, pos, direction):
        """Quietly cache the next image in the direction of travel (disk cache only)."""
        cands = self.cc["cands"]
        if len(cands) < 2:
            return
        nxt = cands[(pos + direction) % len(cands)]
        if nxt["data"] is None and nxt["urls"]:
            threading.Thread(target=lambda: self._safe_fetch(nxt["urls"]), daemon=True).start()

    @staticmethod
    def _safe_fetch(urls):
        try:
            fetch_first_good(urls)
        except Exception:
            pass

    # ---------------------- Find Covers window ---------------------- #
    def open_cover_chooser(self):
        title = self.s_title.get().strip() or self.e["title"].get().strip()
        author = self.s_author.get().strip()
        if not title and not self.results:
            messagebox.showinfo(APP_NAME, "Search for a book first.")
            return
        try:
            if self._cover_win is not None and self._cover_win.winfo_exists():
                self._cover_win.destroy()
        except Exception:
            pass
        win = ctk.CTkToplevel(self)
        win.title("Find Covers")
        win.geometry("640x700")
        win._refs = []
        hdr = ctk.CTkLabel(win, text="Searching for covers…", anchor="w")
        hdr.pack(fill="x", padx=14, pady=(12, 4))
        sc = ctk.CTkScrollableFrame(win)
        sc.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        self._cover_win = win
        win.after(200, win.lift)
        threading.Thread(target=self._chooser_worker,
                         args=(win, hdr, sc, list(self.results), title, author),
                         daemon=True).start()

    def _chooser_worker(self, win, hdr, sc, results, title, author):
        found = 0
        try:
            cands = collect_cover_candidates(results, title, author)
        except Exception as ex:
            log_error(f"cover candidates failed: {ex}")
            cands = []
        for c in cands:
            try:
                data, size = fetch_first_good(c["urls"], first_wins=c.get("first_wins", False))
            except Exception as ex:
                log_error(f"candidate failed ({c['label']}): {ex}")
                continue
            found += 1
            self.post(lambda c=c, d=data, s=size: self._add_cover_row(win, sc, c, d, s))
        self.post(lambda: self._chooser_done(win, hdr, found))

    @staticmethod
    def _alive(win):
        try:
            return bool(win.winfo_exists())
        except Exception:
            return False

    def _add_cover_row(self, win, sc, cand, data, size):
        if not self._alive(win):
            return
        img = Image.open(io.BytesIO(data))
        thumb = img.convert("RGB")
        thumb.thumbnail((110, 110))
        ci = ctk.CTkImage(light_image=thumb, dark_image=thumb, size=thumb.size)
        win._refs.append(ci)
        row = ctk.CTkFrame(sc)
        row.pack(fill="x", pady=4, padx=2)
        row.columnconfigure(1, weight=1)
        ctk.CTkLabel(row, image=ci, text="", width=120).grid(
            row=0, column=0, rowspan=2, padx=8, pady=8)
        ctk.CTkLabel(row, text=cand["label"], anchor="w", justify="left",
                     wraplength=330).grid(row=0, column=1, sticky="sw", padx=4)
        ctk.CTkLabel(row, text=f"{size[0]}×{size[1]}px", anchor="w",
                     text_color=("gray30", "gray70")).grid(row=1, column=1, sticky="nw", padx=4)
        ctk.CTkButton(row, text="Use this", width=90,
                      command=lambda: self._use_cover(win, data, cand["label"])
                      ).grid(row=0, column=2, rowspan=2, padx=10)

    def _chooser_done(self, win, hdr, found):
        if not self._alive(win):
            return
        hdr.configure(text=(f"{found} cover(s) found - click “Use this” to pick one."
                            if found else "No covers found for this book."))

    def _use_cover(self, win, data, label):
        src = label.split(" — ")[0]
        if self.show_cover(data, src):
            self.cgen += 1              # stop any in-flight auto cover from replacing it
            self.set_status(f"Cover set from {src}.")
        try:
            win.destroy()
        except Exception:
            pass

    # ---------------------------------------------------------------------- #
    def load_cover_url(self):
        url = self.url_entry.get().strip()
        if not url:
            return
        self.cgen += 1
        gen = self.cgen
        self.set_status("Downloading cover…")

        def work():
            try:
                data, _ = fetch_first_good([url], good=1)
            except Exception as ex:
                msg = f"Cover download failed: {ex}"
                self.post(lambda: self.set_status(msg))
                return

            def apply():
                if gen != self.cgen:
                    return
                if self.show_cover(data, "URL"):
                    self.set_status("Cover loaded from URL.")
            self.post(apply)
        threading.Thread(target=work, daemon=True).start()

    def upload_cover(self):
        path = filedialog.askopenfilename(
            title="Choose cover image",
            filetypes=[("Images", "*.jpg *.jpeg *.png *.webp *.bmp"), ("All files", "*.*")])
        if not path:
            return
        self.cgen += 1
        if not self.show_cover(Path(path).read_bytes(), "local file"):
            messagebox.showerror(APP_NAME, "That file is not a valid image.")

    def discard(self):
        """Clears the on-screen review only; nothing is written to disk."""
        self.gen += 1
        self.reset_cover_nav()
        if self.mode == MODE_BATCH and self.book_dir is not None:
            self.skipped.add(str(self.book_dir))          # excluded from "Commit all"
        if self.mode == MODE_EDIT and self.book_dir is not None:
            if self.load_existing(self.book_dir):
                self.set_status("Reverted to the saved files. Nothing was written.")
            return
        self.waiting_key = None
        self.clear_form()
        self.clear_cover()
        self.reset_results()
        if self.book_dir is not None:
            self.cache.pop(str(self.book_dir), None)
        self.set_status("Discarded. Nothing was written. Use Re-Scan / Search to try again"
                        + (", or Forward to move on." if self.mode == MODE_BATCH else "."))

    def commit(self):
        """Writes cover.jpg + metadata.json for the book currently on screen ONLY."""
        if self.busy:
            self.set_status("Please wait - a batch operation is running.")
            return
        if not self.book_dir or not self.book_dir.is_dir():
            messagebox.showwarning(APP_NAME, "Select a book folder first.")
            return
        title = self.e["title"].get().strip()
        if not title:
            messagebox.showwarning(APP_NAME, "Title cannot be empty.")
            return

        cover_path = self.book_dir / "cover.jpg"
        meta_path = self.book_dir / "metadata.json"
        existing = [p.name for p in (cover_path, meta_path) if p.exists()]
        editing = self.mode == MODE_EDIT
        if existing and not editing and not messagebox.askyesno(
                APP_NAME, f"{' and '.join(existing)} already exist(s) in\n{self.book_dir}\n\n"
                          "Overwrite?"):
            return

        base = dict(self.existing_meta) if editing else {}
        chapters = (base.get("chapters") if editing and base.get("chapters")
                    else build_chapters(self.book_dir))
        fields = {k: self.e[k].get() for k in self.e}
        meta = compose_meta(fields, self.abridged.get(), self.explicit.get(),
                            self.desc.get("1.0", "end-1c"), self._published_date, chapters)
        meta = {**base, **meta}               # keep any extra keys already in the file
        unchanged_cover = (editing and cover_path.exists()
                           and self.cover_bytes == self.existing_cover_bytes)
        try:
            if self.cover_bytes and not unchanged_cover:
                save_cover_jpg(self.cover_bytes, cover_path)
            atomic_write(meta_path, json.dumps(meta, indent=2, ensure_ascii=False)
                         .encode("utf-8"))
        except Exception as ex:
            messagebox.showerror(APP_NAME, f"Failed to write files:\n{ex}")
            return

        self.committed.add(str(self.book_dir))
        if editing:
            self.existing_meta, self.existing_cover_bytes = meta, self.cover_bytes
        msg = (f"Saved metadata.json{' and cover.jpg' if self.cover_bytes else ''} → "
               f"{self.book_dir}")
        if self.mode == MODE_BATCH:
            self.update_nav()
            self.refresh_batch_buttons()
            self.set_status(msg + "   |   Press Forward for the next book.")
        else:
            self.set_status(msg)
            messagebox.showinfo(APP_NAME, "Files saved.\nRe-scan the library in "
                                          "Audiobookshelf to pick up the changes.")


if __name__ == "__main__":
    App().mainloop()
