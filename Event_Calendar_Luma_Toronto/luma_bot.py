"""
Luma Toronto → Telegram Bot
Scrapes Toronto events from Luma's public discovery API only (no community
page scraping — that was removed for speed; it relied on Playwright/headless
Chromium and was significantly slower than the API call).
Commands: /pull /thisweek /next2weeks /today /watch /clear

Review cards (Today / This Week / Next 2 Weeks / Pull Review) show one event
at a time: the event name is itself a tappable link to its Luma page, with a
"Next ➡️" button to advance to the next card in the queue. No calendar
integration — there is no Accept/Reject step and nothing is added to any
calendar; tapping the event name just opens the Luma page in the browser.

Required env vars:
  TELEGRAM_BOT_TOKEN   — bot token from @BotFather
  TELEGRAM_CHAT_ID     — chat/group to post into
  POLL_INTERVAL_SECS   — (optional) scrape interval, default 3600
"""

import os, json, logging, hashlib, asyncio, time, re
from typing import Any
import numpy as np
from io import BytesIO
from datetime import datetime, timezone, timedelta, time as dt_time
from pathlib import Path
from dotenv import load_dotenv
load_dotenv()

import requests as req
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry  # urllib3 ships as a direct dependency of requests
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, KeyboardButton, ReplyKeyboardMarkup, Update
from telegram.error import TelegramError, TimedOut
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, filters
from telegram.helpers import escape_markdown

# ── CONFIG ────────────────────────────────────────────────────────────────────
TELEGRAM_BOT_TOKEN = os.environ["TELEGRAM_BOT_TOKEN"]
TELEGRAM_CHAT_ID   = os.environ["TELEGRAM_CHAT_ID"]
POLL_INTERVAL_SECS = int(os.getenv("POLL_INTERVAL_SECS", "3600"))
SEEN_DB_PATH       = Path(__file__).parent / "seen_events.json"

# Image download tuning for batch photo sends (Watch Events / morning digest).
# Downloads run in parallel, so the batch deadline must comfortably exceed
# the per-image timeout -- otherwise a single slow image trips the *whole
# batch* deadline before it even gets a chance to time out on its own, and
# every photo (including ones that already finished) used to get thrown
# away. Photos that finish before the deadline are now always kept; only
# the ones still in flight when the deadline hits are dropped.
IMAGE_PER_REQUEST_TIMEOUT_SECS = 10    # per-image connect+read timeout
IMAGE_BATCH_DEADLINE_SECS      = 25    # wall-clock cap for the whole parallel batch
# Bumped from 6s/12s: those were tuned against a home connection's latency to
# Luma's CDN. A cloud host's egress path can be slower/more variable, and the
# scraper-side event-loop-blocking bug (see scrape_luma_toronto) made timeouts
# trip more than they should have on top of that -- extra headroom here so a
# merely-slow-not-broken image still gets through even before that fix lands
# everywhere it matters.
MAX_IMAGE_BYTES                = 9_500_000  # stay under Telegram's 10 MB photo limit

BROWSER_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/125.0.0.0 Safari/537.36"
    ),
    "Accept":  "application/json",
    "Origin":  "https://luma.com",
    "Referer": "https://luma.com/toronto",
}

logging.basicConfig(format="%(asctime)s [%(levelname)s] %(message)s", level=logging.INFO)
log = logging.getLogger(__name__)

# NOTE: fixed UTC-4 — correct for EDT (roughly Mar-Nov) but one hour off
# during EST. Swap for `zoneinfo.ZoneInfo("America/Toronto")` if you need
# correct behaviour across the DST boundary; left as a fixed offset here to
# avoid pulling in tzdata as a new dependency.
TORONTO_TZ = timezone(timedelta(hours=-4))

DEFAULT_DIGEST_HOUR_ET = 7                    # 7 AM Toronto time
DIGEST_HOUR_CHOICES    = list(range(6, 13))   # 6 AM through 12 PM, inclusive
WATCH_BATCH_SIZE       = 3                    # events sent per /watch tap
PERIOD_REFRESH_SECS    = 3600                 # re-check live events at most once/hour while paginating

def _digest_time_utc(hour_et: int) -> dt_time:
    """UTC time object for a given Toronto-local hour (24h, 0-23)."""
    return dt_time(hour=(hour_et + 4) % 24, minute=0, tzinfo=timezone.utc)

def _format_elapsed(start: float) -> str:
    """Format the elapsed time since `start` (a time.perf_counter() value)
    as 'Xs Yms' for logging — e.g. '0s 312ms', '2s 047ms'."""
    elapsed = time.perf_counter() - start
    secs = int(elapsed)
    millis = int((elapsed - secs) * 1000)
    return f"{secs}s {millis:03d}ms"

def _format_hour_et(hour_et: int) -> str:
    """Friendly 12-hour label, e.g. 6 -> '6 AM', 12 -> '12 PM'."""
    suffix = "AM" if hour_et < 12 else "PM"
    display_hour = hour_et if 1 <= hour_et <= 12 else (12 if hour_et == 0 else hour_et - 12)
    return f"{display_hour} {suffix}"

# ── SEEN DB ───────────────────────────────────────────────────────────────────

def load_seen() -> dict:
    db = json.loads(SEEN_DB_PATH.read_text()) if SEEN_DB_PATH.exists() else {}
    db.setdefault("seen", [])
    db.setdefault("events", {})
    db.setdefault("watch_seen", [])  # events already shown via Watch Events
    db.setdefault("morning_digest", True)      # on by default for new installs
    db.setdefault("new_event_alerts", True)    # push alert when a matching event is newly scraped
    db.setdefault("alert_seen", [])            # event IDs already sent as new-event alerts (never cleared by Reset)
    db.setdefault("digest_hour", DEFAULT_DIGEST_HOUR_ET)  # Toronto-local hour (6-12) for the morning digest
    db.setdefault("preferred_categories", [])  # user's chosen categories, most-relevant-first sort
    return db

def save_seen(db: dict):
    SEEN_DB_PATH.write_text(json.dumps(db, indent=2, default=str))

def event_id(event: dict) -> str:
    key = event.get("url") or f"{event.get('title')}|{event.get('start_at', '')}"
    return hashlib.sha1(key.encode()).hexdigest()[:16]

def get_db(context: ContextTypes.DEFAULT_TYPE) -> dict:
    if "db" not in context.bot_data:
        context.bot_data["db"] = load_seen()
    return context.bot_data["db"]

# ── SCRAPER ───────────────────────────────────────────────────────────────────

async def scrape_luma_toronto() -> list[dict]:
    """Fetch Toronto events from Luma's public discovery API only.
    Community-page scraping (via Playwright) was removed — it was slow
    (headless browser + scrolling per page) and pulled in events from
    specific community calendars that were never requested."""
    all_events = []
    url, cursor, page = "https://api.luma.com/discover/get-paginated-events", None, 0

    while page < 20:
        params = {"discover_place_api_id": "discplace-Cx3JMS6vXKAbhV5", "pagination_limit": 25}
        if cursor:
            params["pagination_cursor"] = cursor

        try:
            # req.get() + _normalize() (which can trigger a CPU-bound
            # sentence-transformer embedding per event) are both synchronous/
            # blocking. Run them in a worker thread rather than straight in
            # this coroutine -- otherwise they freeze the bot's *entire*
            # event loop for as long as they take, stalling every other
            # coroutine, including the asyncio.wait() deadline check in
            # _download_images_batch that governs sticker sends. This is
            # the actual cause of the Railway-only missing/partial-sticker
            # bug: a slower or higher-latency path to Luma's API (vs. a
            # home connection) means this blocking window is longer there,
            # so an in-flight sticker batch's timeout gets checked late and
            # images that would've finished in time get cancelled instead.
            def _fetch_and_normalize_page():
                r = req.get(url, params=params, headers=BROWSER_HEADERS, timeout=15)
                if r.status_code != 200:
                    return r.status_code, None, [], []
                d = r.json()
                raw_items = d.get("entries") or d.get("events") or []
                out = []
                for item in raw_items:
                    ev = item.get("event", item)
                    if isinstance(ev, dict) and (ev.get("name") or ev.get("title")):
                        out.append(_normalize(ev))
                return 200, d, raw_items, out

            status, data, raw, normalized = await asyncio.to_thread(_fetch_and_normalize_page)
            if status != 200:
                log.error("Toronto API returned %d on page %d", status, page)
                break
            if not raw:
                break

            all_events.extend(normalized)
            page  += 1
            cursor = data.get("next_cursor")
            log.info("Toronto API page %d: %d events (total: %d)", page, len(raw), len(all_events))
            if not cursor:
                break

        except (req.RequestException, json.JSONDecodeError, KeyError) as e:
            log.error("Toronto API error: %s", e)
            break

    seen_urls, unique = set(), []
    for ev in all_events:
        k = ev.get("url") or ev.get("title")
        if k and k not in seen_urls:
            seen_urls.add(k)
            unique.append(ev)

    log.info("Total unique events: %d", len(unique))
    return unique

# ── CATEGORIES ────────────────────────────────────────────────────────────────
#
# Used for "most relevant first" sorting against a user's chosen
# categories (see preferred_categories in the DB). Two-step extraction:
# 1) try a handful of plausible field names Luma's API might expose this
#    under (none confirmed from a live response — api.luma.com isn't
#    reachable for direct inspection from this environment — so this is
#    deliberately defensive, same pattern as image_url's multi-key probe)
# 2) if no real field matches, keyword-match the title against the
#    buckets below. "Uncategorized" is the deliberate fallback for any
#    event that matches neither — it's excluded from "relevant" results
#    but never silently dropped from the underlying event list.

CATEGORIES = [
    "AI & Tech",
    "Founders & Startups",
    "Workshops & Classes",
    "Talks & Panels",
    "Arts & Culture",
    "Social & Community",
    "Wellness & Fitness",
    "Food & Drink",
    "Gaming & Nightlife",
]

# Representative phrases that define each category's semantic centre.
# The embedding model averages these into one vector per category at startup;
# more phrases = a more stable centroid but a slightly slower startup.
_CATEGORY_ANCHORS: dict[str, list[str]] = {
    "AI & Tech": [
        "artificial intelligence meetup", "machine learning talk",
        "deep learning workshop", "software engineering event",
        "developer community", "LLM hackathon", "OpenAI GPT event",
        "data science networking", "tech startup demo", "coding bootcamp",
        "web3 crypto blockchain", "computer vision NLP",
    ],
    "Founders & Startups": [
        "startup pitch competition", "founder networking night",
        "venture capital demo day", "entrepreneur meetup",
        "early stage startup investors", "VC funding panel",
        "product launch event", "startup ecosystem",
    ],
    "Workshops & Classes": [
        "hands-on workshop", "skill building class",
        "professional training session", "masterclass tutorial",
        "learn new skills", "interactive bootcamp",
        "guided learning session", "practitioner workshop",
    ],
    "Talks & Panels": [
        "keynote speaker talk", "panel discussion",
        "fireside chat", "speaker series lecture",
        "industry thought leadership", "expert presentation",
        "Q&A with speakers", "moderated debate",
    ],
    "Arts & Culture": [
        "film screening", "art gallery opening",
        "museum exhibit", "theatre performance",
        "poetry reading", "live music concert",
        "comedy show", "cultural festival",
        "creative arts showcase",
    ],
    "Social & Community": [
        "networking mixer", "community coffee chat",
        "social happy hour", "neighbourhood gathering",
        "casual meetup", "friends social event",
        "community volunteer", "local group hangout",
    ],
    "Wellness & Fitness": [
        "yoga class", "meditation session",
        "group fitness training", "running club",
        "mental health wellness", "mindfulness retreat",
        "outdoor hike", "workout class",
    ],
    "Food & Drink": [
        "wine tasting", "dinner party",
        "brunch event", "cocktail evening",
        "food festival", "culinary experience",
        "beer tasting", "supper club",
    ],
    "Gaming & Nightlife": [
        "board game night", "trivia contest",
        "video game tournament", "DJ dance party",
        "nightclub rave", "escape room",
        "poker night", "gaming community",
    ],
}

# ── EMBEDDING MODEL (lazy-loaded) ─────────────────────────────────────────────
# Loaded once on first categorisation call; None if sentence-transformers is
# not installed (falls back to Uncategorized with a warning).

_embedding_model: Any = None  # SentenceTransformer instance once loaded
_category_vectors: dict[str, np.ndarray] = {}  # pre-averaged anchor vectors

def _load_embedding_model() -> bool:
    """Load the embedding model and pre-compute per-category centroid vectors.
    Returns True on success, False if sentence-transformers is unavailable."""
    global _embedding_model, _category_vectors
    if _embedding_model is not None:
        return True
    try:
        from sentence_transformers import SentenceTransformer
        log.info("Loading sentence-transformers model (all-MiniLM-L6-v2)…")
        _embedding_model = SentenceTransformer("all-MiniLM-L6-v2")
        for cat, phrases in _CATEGORY_ANCHORS.items():
            vecs = _embedding_model.encode(phrases, convert_to_numpy=True)
            _category_vectors[cat] = vecs.mean(axis=0)
        log.info("Embedding model ready. %d category vectors computed.", len(_category_vectors))
        return True
    except Exception as exc:
        log.warning("sentence-transformers unavailable — categories will be 'Uncategorized': %s", exc)
        return False

def _cosine_classify(text: str) -> str:
    """Return the category whose centroid vector is closest to `text`."""
    event_vec = _embedding_model.encode(text, convert_to_numpy=True)
    best_cat, best_score = "Uncategorized", -1.0
    for cat, cat_vec in _category_vectors.items():
        magnitude = np.linalg.norm(event_vec) * np.linalg.norm(cat_vec)
        score = float(np.dot(event_vec, cat_vec) / magnitude) if magnitude > 0 else 0.0
        if score > best_score:
            best_score, best_cat = score, cat
    return best_cat

def _extract_category(raw_event: dict) -> str:
    """Best-effort category for a raw Luma API event object (called from
    _normalize, before the event is flattened).

    Step 1 — real API fields: tries a handful of field names the Luma API
    might expose (none confirmed from live responses, but checked first so
    official data is always preferred over inference).

    Step 2 — semantic embedding similarity: encodes the event title with
    all-MiniLM-L6-v2 and picks the category whose pre-averaged anchor
    vector has the highest cosine similarity. Understands context, brand
    names (OpenAI, Anthropic, etc.), and phrasing nuance that keyword
    matching misses entirely.

    Falls back to "Uncategorized" only if sentence-transformers is not
    installed or the model fails to load."""
    # Step 1: prefer any real category field the API provides.
    for key in ("category", "category_name", "discovery_category", "tag"):
        val = raw_event.get(key)
        if isinstance(val, str) and val.strip():
            return val.strip()
        if isinstance(val, dict) and val.get("name"):
            return str(val["name"]).strip()
    for key in ("tags", "categories"):
        val = raw_event.get(key)
        if isinstance(val, list) and val:
            first = val[0]
            if isinstance(first, str) and first.strip():
                return first.strip()
            if isinstance(first, dict) and first.get("name"):
                return str(first["name"]).strip()

    # Step 2: semantic classification via cosine similarity.
    title = (raw_event.get("name") or raw_event.get("title") or "").strip()
    if not title:
        return "Uncategorized"

    if not _load_embedding_model():
        return "Uncategorized"

    try:
        return _cosine_classify(title)
    except Exception as exc:
        log.warning("Cosine classification failed for %r: %s", title, exc)
        return "Uncategorized"

def _normalize(e: dict) -> dict:
    url = e.get("url") or e.get("event_url") or ""
    if url and not url.startswith("http"):
        url = f"https://luma.com/{url}"

    # Luma's API has used a few different keys for the cover image across
    # versions/endpoints — fall back gracefully; if none match, image_url
    # stays empty and the bot just skips the photo for that event.
    image_url = (
        e.get("cover_url")
        or e.get("image_url")
        or (e.get("cover_image") or {}).get("url")
        or (e.get("event_cover") or {}).get("url")
        or ""
    )

    return {
        "title":     e.get("name") or e.get("title") or "Untitled",
        "start_at":  e.get("start_at") or e.get("startAt") or "",
        "end_at":    e.get("end_at")   or e.get("endAt")   or "",
        "location":  (e.get("geo_address_info") or {}).get("full_address") or e.get("location") or "",
        "url":       url,
        "image_url": image_url,
        "category":  _extract_category(e),
    }

# ── DATE HELPERS ──────────────────────────────────────────────────────────────

def _parse_dt(s: str) -> datetime:
    if not s:
        return datetime.now(timezone.utc)
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00"))
    except (ValueError, AttributeError):
        return datetime.now(timezone.utc)

def _to_toronto(s: str) -> datetime | None:
    """Parse + convert to Toronto local time; None if parsing meaningfully fails."""
    try:
        return _parse_dt(s).astimezone(TORONTO_TZ)
    except (ValueError, AttributeError, OSError):
        return None

def fmt_date(start: str, end: str = "") -> str:
    """Full 'Sat Jun 21 · 6:00 PM – 8:00 PM ET' label used on review cards."""
    dt = _to_toronto(start)
    if dt is None:
        return start or "TBD"
    out = dt.strftime("%a %b %d · %I:%M %p")
    if end:
        out += _to_toronto(end).strftime(" – %I:%M %p")
    return out + " ET"

def fmt_start_only(start: str) -> str:
    """Short 'Sat Jun 21 · 6:00 PM' label (no end time, no 'ET' suffix) —
    used in batch summaries (Watch Events / morning digest) where 5-10
    events need to fit on one screen without scrolling."""
    dt = _to_toronto(start)
    if dt is None:
        return start or "TBD"
    hour = dt.hour % 12 or 12  # no leading zero, e.g. "6:00 PM" not "06:00 PM"
    return f"{dt.strftime('%a %b %d')} · {hour}{dt.strftime(':%M %p')}"

# ── MESSAGE BUILDERS ──────────────────────────────────────────────────────────

def build_message(event: dict) -> tuple[str, InlineKeyboardMarkup]:
    """Build a one-event review card: the event name itself is a tappable
    MarkdownV2 hyperlink to its Luma page (no separate "Accept" action or
    calendar integration — tapping the name just opens the page), date/
    time and location combined onto one line to keep the card short, and
    a single "Next ➡️" button to advance the queue."""
    eid   = event_id(event)
    title = escape_markdown(event.get("title", "Untitled"), version=2)
    url   = event.get("url", "")
    title_line = f"*[{title}]({url})*" if url else f"*{title}*"

    when = fmt_date(event.get("start_at", ""), event.get("end_at", ""))
    line2 = f"🕐 {when}"
    if event.get("location"):
        line2 += f" · 📍 {_short_address(event['location'])}"

    text = f"📅 {title_line}\n{escape_markdown(line2, version=2)}\n"
    kbd = InlineKeyboardMarkup([[InlineKeyboardButton("Next ➡️", callback_data=f"next|{eid}")]])
    return text, kbd

# ── CALLBACK HANDLER ──────────────────────────────────────────────────────────

async def _delete_or_clear_buttons(query, context: ContextTypes.DEFAULT_TYPE):
    """Delete the card's message; if that fails (message already gone, no
    usable chat_id, etc.) fall back to stripping its buttons so it can't be
    tapped again."""
    chat_id = query.message.chat.id if query.message else None
    try:
        if chat_id is not None:
            await context.bot.delete_message(chat_id=chat_id, message_id=query.message.message_id)
            return
    except TelegramError as e:
        log.warning("Delete failed, clearing buttons instead: %s", e)
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except TelegramError:
        pass

async def handle_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle a tap on a review card's "Next ➡️" button: delete the current
    card and advance to the next one in that chat's review queue. No
    accept/reject branching and no calendar integration — the event name
    on the card is already a direct link to its Luma page."""
    query = update.callback_query
    await query.answer()

    _, eid = query.data.split("|", 1)
    pending = context.bot_data.setdefault("pending", {})
    entry   = pending.pop(eid, None)

    await _delete_or_clear_buttons(query, context)

    # Stale button (bot restarted, entry no longer tracked) — nothing to advance.
    if not entry:
        return

    review_chat_id = entry.get("review_chat_id")
    if review_chat_id is not None:
        await _send_review_card(review_chat_id, context)

async def handle_digest_time_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle a tap on the inline hourly time picker for the morning digest.
    Separate from handle_callback (which only deals with next| review-card
    buttons) so the two callback_data namespaces never collide."""
    query = update.callback_query
    await query.answer()

    hour_et = int(query.data.split("|", 1)[1])
    db = get_db(context)
    was_enabled = db.get("morning_digest", False)

    db["morning_digest"], db["digest_hour"] = True, hour_et
    save_seen(db)
    _schedule_morning_digest(context.job_queue, hour_et)

    verb = "rescheduled" if was_enabled else "enabled"
    try:
        await query.edit_message_text(
            f"✅ *Morning Digest {verb}!*\nYou'll get today's events every day at "
            f"*{_format_hour_et(hour_et)}* Toronto time.",
            parse_mode="Markdown",
            reply_markup=_build_time_picker(hour_et),
        )
    except TelegramError as e:
        log.error("Failed to update time-picker message: %s", e)

# ── POLLER ────────────────────────────────────────────────────────────────────

async def poll_luma(context: ContextTypes.DEFAULT_TYPE):
    """Fetch and store events, then prune anything that has already happened.
    Without pruning, events/seen/watch_seen would grow without bound,
    slowing every JSON read/write as the bot runs for months.

    New-event alerts: any event discovered for the first time after the
    initial startup poll is pushed immediately to the chat if it matches
    the user's preferred_categories (or unconditionally if no preference
    is set). The startup poll is suppressed so the bot doesn't flood the
    chat with every existing event on first boot."""
    log.info("Polling Luma Toronto…")
    db        = get_db(context)
    events    = await scrape_luma_toronto()
    new_count = 0
    new_events: list[dict] = []

    # Suppress alerts on the very first poll (bot startup) — every event
    # would look "new" to an empty seen list, causing a flood.
    is_startup_poll = not context.bot_data.get("initial_poll_done", False)

    # Lookup set built once instead of an O(n) "in" check per event against
    # the raw list (which would be O(n*m) overall as the list grows).
    seen_set       = set(db["seen"])
    alert_seen_set = set(db.get("alert_seen", []))  # separate from seen — not cleared by Reset Progress

    for ev in events:
        eid = event_id(ev)
        db["events"][eid] = ev
        if eid not in seen_set:
            db["seen"].append(eid)
            seen_set.add(eid)
            new_count += 1
        if not is_startup_poll and eid not in alert_seen_set:
            new_events.append(ev)
            alert_seen_set.add(eid)

    pruned = _prune_past_events(db)
    save_seen(db)
    context.bot_data["initial_poll_done"] = True

    if new_events:
        await _send_new_event_alerts(context, db, new_events)

    log.info("Poll done. %d new event(s) stored, %d past event(s) pruned.", new_count, pruned)

NEW_EVENT_ALERTS_CAP = 5   # max stickers per poll cycle to avoid flooding

async def _send_new_event_alerts(context: ContextTypes.DEFAULT_TYPE, db: dict, new_events: list[dict]):
    """Push sticker+text cards for newly discovered events that match the
    user's preferred_categories (all new events if no preference is set).
    Capped at NEW_EVENT_ALERTS_CAP per poll cycle; any overflow is noted
    in a trailing message so the user knows to /watch for the rest."""
    if not db.get("new_event_alerts", True):
        return

    preferred = set(db.get("preferred_categories", []))
    matching  = [e for e in new_events if not preferred or e.get("category") in preferred]
    if not matching:
        return

    chat_id  = int(TELEGRAM_CHAT_ID)
    batch    = matching[:NEW_EVENT_ALERTS_CAP]
    overflow = len(matching) - len(batch)

    # Persist alert_seen before sending so a crash mid-send never causes a re-alert.
    db.setdefault("alert_seen", []).extend(event_id(e) for e in matching)
    save_seen(db)

    cats_label = f" in *{', '.join(sorted(preferred))}*" if preferred else ""
    count      = len(batch)
    await context.bot.send_message(
        chat_id=chat_id,
        text=f"🆕 *{count} new event{'s' if count != 1 else ''}{cats_label} just listed on Luma!*",
        parse_mode="Markdown",
    )
    await _send_events_as_stickers(chat_id, context, batch)

    if overflow:
        await context.bot.send_message(
            chat_id=chat_id,
            text=f"…and {overflow} more new event{'s' if overflow != 1 else ''}. Tap *👀 Watch Events* to see them.",
            parse_mode="Markdown",
        )

def _prune_past_events(db: dict) -> int:
    """Drop events whose start time has passed and scrub their IDs out of
    seen/watch_seen."""
    now = datetime.now(timezone.utc)
    past_ids = {eid for eid, ev in db["events"].items() if _parse_dt(ev.get("start_at", "")) < now}
    if not past_ids:
        return 0

    for eid in past_ids:
        db["events"].pop(eid, None)
    for key in ("seen", "watch_seen", "alert_seen"):
        db[key] = [eid for eid in db.get(key, []) if eid not in past_ids]

    return len(past_ids)

# ── REVIEW MODE (one-by-one, scoped to a time period) ────────────────────────
#
# Each "review" is a queue of events for a given period. Cards are sent one
# at a time; tapping "Next ➡️" on a card deletes it and automatically sends
# the next one in that queue. When the queue empties, a single "done"
# message is sent.
#
# All filters share one core routine: parse each event's start time exactly
# once, apply a predicate, then sort chronologically — avoids re-parsing the
# same date string multiple times per event.

def _filter_events(db: dict, predicate) -> list[dict]:
    """Events whose parsed start datetime satisfies predicate(dt, event).
    If the user has chosen preferred_categories, matching events are
    sorted first (chronologically among themselves), followed by
    everything else (also chronologically) — two time-ordered groups
    stacked together, not a single re-ranked list. This keeps the
    within-group ordering predictable (still "soonest first") rather than
    scrambling chronology entirely in the name of relevance. No
    preference set → falls back to plain chronological order, unchanged
    from before this feature existed."""
    matches = []
    for e in db.get("events", {}).values():
        dt = _parse_dt(e.get("start_at", ""))
        if predicate(dt, e):
            matches.append((e.get("start_at", ""), e))
    matches.sort(key=lambda pair: pair[0])

    preferred = set(db.get("preferred_categories", []))
    if not preferred:
        return [e for _, e in matches]

    relevant    = [e for _, e in matches if e.get("category") in preferred]
    rest        = [e for _, e in matches if e.get("category") not in preferred]
    return relevant + rest

def _filter_today(db: dict) -> list[dict]:
    today = datetime.now(timezone.utc).astimezone(TORONTO_TZ).date()
    return _filter_events(db, lambda dt, _e: dt.astimezone(TORONTO_TZ).date() == today)

def _filter_window(db: dict, days: int) -> list[dict]:
    """Events starting between now and `days` from now (rolling window)."""
    now, end = datetime.now(timezone.utc), datetime.now(timezone.utc) + timedelta(days=days)
    return _filter_events(db, lambda dt, _e: now <= dt < end)

def _filter_watch_unseen(db: dict) -> list[dict]:
    """Upcoming events not yet shown via Watch Events, soonest first (with
    preferred-category sorting applied on top, same as every other list).
    Uses its own 'watch_seen' tracking, independent of the review-card
    'seen' list, so /watch and /today /thisweek /next2weeks never step on
    each other's progress."""
    now, watch_seen = datetime.now(timezone.utc), set(db.get("watch_seen", []))
    return _filter_events(db, lambda dt, e: dt >= now and event_id(e) not in watch_seen)

def _filter_all_upcoming(db: dict) -> list[dict]:
    now = datetime.now(timezone.utc)
    return _filter_events(db, lambda dt, _e: dt >= now)

def _range_label(span_days: int) -> str:
    """Toronto-local 'Mon Jun 21 → Sun Jun 27' label spanning `span_days`."""
    now = datetime.now(timezone.utc)
    start = now.astimezone(TORONTO_TZ).strftime("%a %b %d")
    end   = (now + timedelta(days=span_days)).astimezone(TORONTO_TZ).strftime("%a %b %d")
    return f"{start} → {end}"

async def _send_review_card(chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    """Pop the next event off this chat's review queue and send it as a
    one-event card (event name is a tappable link, "Next ➡️" advances);
    send the period's "all done" message once the queue is empty."""
    reviews = context.bot_data.setdefault("reviews", {})
    state   = reviews.get(chat_id)
    if not state:
        return  # no active review for this chat

    queue = state["queue"]
    if not queue:
        await context.bot.send_message(chat_id=chat_id, text=state["done_message"])
        reviews.pop(chat_id, None)
        return

    event = queue.pop(0)
    eid = event_id(event)
    text, kbd = build_message(event)
    await context.bot.send_message(
        chat_id=chat_id, text=text, parse_mode="MarkdownV2", reply_markup=kbd,
    )
    # Tag this card with its chat_id so the callback knows how to advance the queue.
    context.bot_data.setdefault("pending", {})[eid] = {"event": event, "review_chat_id": chat_id}

async def _start_review(update: Update, context: ContextTypes.DEFAULT_TYPE, events: list[dict],
                         intro: str, empty: str, done: str):
    """Kick off a one-by-one review: seed the chat's review queue and send
    the first card."""
    if not events:
        await update.message.reply_text(empty)
        return
    await update.message.reply_text(intro, parse_mode="Markdown")
    chat_id = update.effective_chat.id
    context.bot_data.setdefault("reviews", {})[chat_id] = {"queue": events, "done_message": done}
    await _send_review_card(chat_id, context)

async def _ensure_events(update: Update, context: ContextTypes.DEFAULT_TYPE) -> dict:
    """Scrape on demand if the cache is empty, so date-range commands work
    even before a /pull."""
    db = get_db(context)
    if not db.get("events"):
        notice = await update.message.reply_text("🔍 Fetching events…")
        await poll_luma(context)
        db = get_db(context)
        try:
            await notice.delete()
        except TelegramError:
            pass
    return db

# Each entry: (filter_fn, label_fn, icon, scope). scope picks which message
# matches "today"/"this week"/etc; icon + label feed the shared message
# templates below. This table replaces four near-identical command bodies.
_REVIEW_PERIODS = {
    "today":       dict(filter=lambda db: _filter_today(db),
                         label=lambda: f"today — {datetime.now(timezone.utc).astimezone(TORONTO_TZ).strftime('%b %d')}",
                         icon="📅", noun="today"),
    "thisweek":    dict(filter=lambda db: _filter_window(db, 7),
                         label=lambda: f"this week — {_range_label(6)}",
                         icon="📋", noun="this week"),
    "next2weeks":  dict(filter=lambda db: _filter_window(db, 14),
                         label=lambda: f"in the next 2 weeks — {_range_label(13)}",
                         icon="📅", noun="in the next 2 weeks"),
}

async def _run_period_review(period: str, update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Shared body for /today, /thisweek, /next2weeks: fetch (if needed),
    filter to the period, and start batched sticker+text pagination
    (WATCH_BATCH_SIZE events at a time, "Show more" button for the rest).
    Does NOT use the older one-by-one review
    queue; that's still exclusive to /pull's post-fetch review."""
    spec   = _REVIEW_PERIODS[period]
    db     = await _ensure_events(update, context)
    events = spec["filter"](db)
    label  = spec["label"]()
    await _start_period_batch(
        update, context, period, events,
        intro=f"{spec['icon']} *Events {label}* ({len(events)} total):",
        empty=f"No events {spec['noun']}.",
    )

# ── BATCH PAGINATION (sticker+text pairs, N at a time + "Show more") ────────
#
# Shared by /today, /thisweek, /next2weeks: send up to WATCH_BATCH_SIZE
# events as sticker+text pairs, then a "Show N more" button if more
# remain. Tapping the button sends the next batch the same way.
#
# Unlike a plain frozen snapshot, each queue also re-checks against the
# live event database once PERIOD_REFRESH_SECS has elapsed since it was
# last refreshed — so an event discovered by a background /pull poll
# while a user is mid-pagination eventually gets folded in (within the
# hour), in its correct chronological position, without ever re-showing
# something already sent. Queues are stored in
# bot_data["period_queues"], keyed by (chat_id, period); each entry is
# {"remaining": [...], "shown_ids": {...}, "refreshed_at": float}.
#
# This is a distinct mechanism from bot_data["reviews"] (the older
# one-by-one Next-button cards), which only /pull's review still uses —
# that one is intentionally untouched by any of this.

def _refresh_period_queue(context: ContextTypes.DEFAULT_TYPE, chat_id: int, period: str):
    """Re-run this period's filter against the live event database and
    merge the result into the existing queue: events already shown this
    run (tracked in shown_ids) are excluded, and anything newly
    discovered is folded in at its correct chronological position
    relative to whatever was already queued (re-filtering naturally
    re-sorts everything together, since _filter_events always sorts).
    No-op if the queue doesn't exist or isn't due for a refresh yet."""
    queues = context.bot_data.setdefault("period_queues", {})
    key = (chat_id, period)
    state = queues.get(key)
    if not state:
        return
    if time.monotonic() - state["refreshed_at"] < PERIOD_REFRESH_SECS:
        return

    db = get_db(context)
    fresh = _REVIEW_PERIODS[period]["filter"](db)
    state["remaining"] = [e for e in fresh if event_id(e) not in state["shown_ids"]]
    state["refreshed_at"] = time.monotonic()
    log.info("Period queue refreshed: chat=%s period=%s remaining=%d",
              chat_id, period, len(state["remaining"]))

async def _send_period_batch(chat_id: int, context: ContextTypes.DEFAULT_TYPE, period: str):
    """Pop up to WATCH_BATCH_SIZE events off this chat's queue for
    `period` and send them as sticker+text pairs, then a "Show N more"
    button if any remain. Used by /today, /thisweek, /next2weeks only —
    /watch uses its own simpler cache-only mechanism (_filter_watch_unseen
    + watch_seen), not this queue system at all. Refreshes the queue
    against the live event list first if it's been more than
    PERIOD_REFRESH_SECS since the last refresh. Safe to call with an
    empty/missing queue (no-op)."""
    queues = context.bot_data.setdefault("period_queues", {})
    key = (chat_id, period)

    _refresh_period_queue(context, chat_id, period)
    state = queues.get(key)
    if not state or not state["remaining"]:
        queues.pop(key, None)
        return

    batch, remaining = state["remaining"][:WATCH_BATCH_SIZE], state["remaining"][WATCH_BATCH_SIZE:]
    state["remaining"] = remaining
    state["shown_ids"].update(event_id(e) for e in batch)

    await _send_events_as_stickers(chat_id, context, batch)

    if not remaining:
        queues.pop(key, None)
    else:
        kbd = InlineKeyboardMarkup([[
            InlineKeyboardButton(f"Show {min(len(remaining), WATCH_BATCH_SIZE)} more",
                                  callback_data=f"periodmore|{period}"),
        ]])
        await context.bot.send_message(chat_id=chat_id, text=f"{len(remaining)} more.", reply_markup=kbd)

async def _start_period_batch(update: Update, context: ContextTypes.DEFAULT_TYPE, period: str,
                               events: list[dict], intro: str, empty: str):
    """Kick off batched sticker+text pagination for `period`: seed the
    chat's queue (with a fresh refresh timestamp) and send the first
    batch."""
    if not events:
        await update.message.reply_text(empty)
        return
    await update.message.reply_text(intro, parse_mode="Markdown")
    chat_id = update.effective_chat.id
    context.bot_data.setdefault("period_queues", {})[(chat_id, period)] = {
        "remaining": events,
        "shown_ids": set(),
        "refreshed_at": time.monotonic(),
    }
    await _send_period_batch(chat_id, context, period)

async def handle_period_more_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle a tap on a "Show N more" button for /today, /thisweek, or
    /next2weeks — sends the next batch from that period's queue for this
    chat, refreshing against the live event list first if due. Separate
    callback_data namespace (periodmore|) from next| (the old one-by-one
    cards, still used by /pull) so taps can't cross-route."""
    query = update.callback_query
    await query.answer()
    _, period = query.data.split("|", 1)
    chat_id = query.message.chat.id

    try:
        await query.edit_message_reply_markup(reply_markup=None)  # button can't be tapped twice
    except TelegramError:
        pass

    await _send_period_batch(chat_id, context, period)

async def cmd_today(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _run_period_review("today", update, context)

async def cmd_thisweek(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _run_period_review("thisweek", update, context)

async def cmd_nexttwoweeks(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _run_period_review("next2weeks", update, context)

async def cmd_pull_review(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """After a fresh /pull, walk through every upcoming event one by one."""
    db     = get_db(context)
    events = _filter_all_upcoming(db)
    await _start_review(
        update, context, events,
        intro=f"🔍 *Reviewing {len(events)} upcoming event(s)* from the latest fetch:",
        empty="No upcoming events found.",
        done="✅ That's all the upcoming events — all reviewed!",
    )

async def cmd_pull(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("🔍 Fetching latest Toronto events…")
    await poll_luma(context)
    db = get_db(context)
    await update.message.reply_text(f"✅ Done! {len(db.get('events', {}))} total events in database.")
    await cmd_pull_review(update, context)

# ── IMAGE HANDLING ────────────────────────────────────────────────────────────

# A shared, thread-safe Session reuses TCP/TLS connections to Luma's CDN
# across the whole batch instead of paying a fresh handshake per image —
# this is usually the single biggest speedup available here, since most of
# a slow "download" is connection setup, not transfer time. A small retry
# (one retry on connection-level errors, no backoff) absorbs the occasional
# dropped connection without burning the per-request timeout twice.
_image_session = req.Session()
_image_session.headers.update(BROWSER_HEADERS)
_image_adapter = HTTPAdapter(
    pool_connections=10, pool_maxsize=10,
    max_retries=Retry(total=1, connect=1, read=0, backoff_factor=0),
)
_image_session.mount("https://", _image_adapter)
_image_session.mount("http://", _image_adapter)

def _download_image(url: str) -> bytes | None:
    """Download an image and return its raw bytes, or None on failure.

    WHY: handing Telegram an image *URL* means Telegram's own servers fetch
    it with a short (~5s) timeout and no retries. Luma's CDN sometimes
    responds slowly or rate-limits Telegram's fetcher in bursts, and
    send_media_group is all-or-nothing — one failed fetch fails the whole
    album. Downloading the bytes ourselves (real timeout + browser-like
    headers, pooled connections) and uploading them directly removes that
    dependency and is also just faster.

    Logging is deliberately verbose on failure (status code + a snippet of
    the response body, or the specific exception type + elapsed time) --
    on a cloud host we can't attach a debugger or watch it happen live, so
    the Railway log line for a given failure has to be enough on its own to
    tell a plain timeout apart from a CDN-side block/rate-limit (e.g. a 403
    or 429, or an HTML challenge page coming back with a 200 and a
    non-image content-type)."""
    if not url:
        return None
    started = time.perf_counter()
    try:
        resp = _image_session.get(url, timeout=IMAGE_PER_REQUEST_TIMEOUT_SECS)
        elapsed = _format_elapsed(started)
        if resp.status_code != 200:
            log.warning("Image fetch returned %d for %s (after %s). Body snippet: %r",
                        resp.status_code, url, elapsed, resp.text[:200])
            return None
        if not resp.headers.get("content-type", "").startswith("image/"):
            log.warning("URL is not an image (content-type=%r) for %s (after %s). Body snippet: %r",
                        resp.headers.get("content-type"), url, elapsed, resp.text[:200])
            return None
        data = _shrink_image(resp.content)  # resize/recompress before size check
        if len(data) > MAX_IMAGE_BYTES:
            log.warning("Image too large (%d bytes) even after shrinking, skipping: %s", len(data), url)
            return None
        return data
    except req.Timeout as e:
        log.warning("Image download TIMED OUT after %s (limit %ds) for %s: %s",
                     _format_elapsed(started), IMAGE_PER_REQUEST_TIMEOUT_SECS, url, e)
        return None
    except req.RequestException as e:
        log.warning("Image download failed after %s for %s: %s: %s",
                     _format_elapsed(started), url, type(e).__name__, e)
        return None

def _shrink_image(data: bytes) -> bytes:
    """Downscale to at most ~1280px wide and re-encode as JPEG to cut upload
    size/time. Big Luma cover images (1-3 MB) are the main reason uploads
    time out; a resized JPEG is usually well under 200 KB. No cropping —
    original aspect ratio is preserved. Best-effort only — if Pillow is
    missing or anything fails, return the original bytes unchanged."""
    try:
        from PIL import Image
    except ImportError:
        return data
    try:
        img = Image.open(BytesIO(data)).convert("RGB")
        max_w = 1280
        if img.width > max_w:
            ratio = max_w / img.width
            img = img.resize((max_w, int(img.height * ratio)))
        out = BytesIO()
        img.save(out, format="JPEG", quality=82, optimize=True)
        return out.getvalue()
    except Exception as e:  # noqa: BLE001 — any decode/encode failure → keep original
        log.warning("Image resize failed, using original bytes: %s", e)
        return data

IMAGE_STAGGER_SECS  = 0.25  # delay between launching each parallel download
RETRY_BUDGET_SECS   = 15    # extra wall-clock budget for the serial second-chance pass

async def _delayed_download(url: str, index: int) -> bytes | None:
    """Same as _download_image, but each index in a batch starts slightly
    later than the last (index * IMAGE_STAGGER_SECS). Firing every request
    in a batch at the exact same instant, from the same source IP, is
    exactly the shape of traffic that CDN/WAF burst- or rate-limiting
    heuristics look for -- and a shared cloud host's egress IP (Railway) is
    far more likely to already be under that kind of scrutiny than a home
    connection's IP, where the same simultaneous-burst pattern went
    unnoticed. Spreading the requests out a little costs at most ~2s for a
    10-image batch, well inside the batch deadline."""
    if index:
        await asyncio.sleep(index * IMAGE_STAGGER_SECS)
    return await asyncio.to_thread(_download_image, url)

async def _download_images_batch(urls: list[str]) -> list[bytes | None]:
    """Download every URL, returning results in the same order as `urls`
    (None for any that failed or didn't finish in time).

    Two passes:
    1. Parallel (staggered) pass, capped at IMAGE_BATCH_DEADLINE_SECS.
       Uses asyncio.wait(..., timeout=...) instead of wait_for(gather(...)):
       wait_for cancels and discards EVERYTHING -- including downloads that
       already finished -- the moment the deadline passes. That meant one
       slow image could blank out several good photos that were sitting
       there done. Here, any task still running once the deadline hits is
       cancelled and counted as a miss, but everything that already
       completed is kept.
    2. Serial second-chance pass over whatever the first pass missed,
       bounded by RETRY_BUDGET_SECS total (not per-image). A dropped
       connection or a momentary rate-limit is often transient -- retrying
       one at a time, well after the original burst, gives those images a
       real chance to come through instead of just being written off."""
    tasks = [asyncio.ensure_future(_delayed_download(u, i)) for i, u in enumerate(urls)]
    done, pending = await asyncio.wait(tasks, timeout=IMAGE_BATCH_DEADLINE_SECS, return_when=asyncio.ALL_COMPLETED)

    if pending:
        log.warning("%d of %d image(s) still downloading past the %ds batch deadline; "
                     "keeping the ones that finished, dropping the rest.",
                     len(pending), len(urls), IMAGE_BATCH_DEADLINE_SECS)
        for t in pending:
            t.cancel()

    results = []
    for t in tasks:
        if t.done() and not t.cancelled():
            try:
                results.append(t.result())
            except Exception as e:  # noqa: BLE001 — a single bad download shouldn't sink the batch
                log.warning("Image download task raised: %s", e)
                results.append(None)
        else:
            results.append(None)

    missing = [i for i, r in enumerate(results) if r is None and urls[i]]
    if missing:
        log.info("First pass missed %d/%d image(s); retrying serially (budget %ds)…",
                  len(missing), len(urls), RETRY_BUDGET_SECS)
        retry_deadline = time.monotonic() + RETRY_BUDGET_SECS
        for n, i in enumerate(missing):
            if time.monotonic() >= retry_deadline:
                log.warning("Serial retry budget exhausted; %d image(s) left unretried.", len(missing) - n)
                break
            retried = await asyncio.to_thread(_download_image, urls[i])
            if retried:
                log.info("Serial retry recovered image for %s", urls[i])
                results[i] = retried
            else:
                log.warning("Serial retry still failed for %s", urls[i])

    return results

# ── WATCH EVENTS ──────────────────────────────────────────────────────────────

_POSTAL_CODE_RE = re.compile(r"[A-Za-z]\d[A-Za-z]\s?\d[A-Za-z]\d")
_STREET_NUMBER_RE = re.compile(r"^\d+[A-Za-z]?\s")

def _short_address(full_address: str) -> str:
    """Reduce a full Luma address ('Venue Name, 60 Sumach St, Toronto, ON
    M5A 3J7, Canada') down to just the street + postal code ('60 Sumach St,
    M5A 3J7') — dropping the venue name, city, province, and country.

    Luma's full_address is one pre-formatted string, not separate
    street/city/province fields, and venue names themselves often contain
    commas (e.g. 'Pluto: Fourth Space for Community, Co-Creation, &
    Coworking, 60 Sumach St...'), so a naive comma-split by position would
    grab the wrong segment. Instead, this anchors on two recognizable
    patterns regardless of position: a Canadian postal code (always
    'LetterDigitLetter DigitLetterDigit') found anywhere via regex, and
    the comma-separated segment that starts with a street number. If
    neither pattern is found (e.g. a short address with no postal code,
    or a venue name with no street number at all), the original string is
    returned unchanged rather than guessing."""
    if not full_address:
        return full_address

    postal_match = _POSTAL_CODE_RE.search(full_address)
    postal = postal_match.group(0).upper().replace(" ", "") if postal_match else None
    if postal and len(postal) == 6:
        postal = f"{postal[:3]} {postal[3:]}"

    parts = [p.strip() for p in full_address.split(",")]
    street = next((p for p in parts if _STREET_NUMBER_RE.match(p)), None)

    if street and postal:
        return f"{street}, {postal}"
    if street:
        return street
    if postal:
        return postal
    return full_address  # no recognizable street/postal found — leave as-is

def _build_document_caption(event: dict) -> str:
    """Caption for an event sent via sendDocument: the event name as a
    bold, tappable MarkdownV2 hyperlink (same nesting trick as
    build_message — legacy Markdown can't nest bold inside a link, so this
    needs MarkdownV2), then date/time and the shortened street + postal
    code (see _short_address) combined onto a single line to keep the
    message as short as possible."""
    title = escape_markdown(event.get("title", "Untitled"), version=2)
    url   = event.get("url", "")
    title_line = f"*[{title}]({url})*" if url else f"*{title}*"

    when = fmt_start_only(event.get("start_at", ""))
    line2 = f"{when} · {_short_address(event['location'])}" if event.get("location") else when
    return f"{title_line}\n{escape_markdown(line2, version=2)}"

def _document_filename(event: dict) -> str:
    """A short, readable filename for the attached image — this is what
    Telegram displays next to the thumbnail in the file-attachment card,
    so a generic name like the raw URL's last path segment would look
    worse than a name derived from the event title."""
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", event.get("title", "event")).strip("-").lower()
    return f"{slug[:50] or 'event'}.jpg"

def _to_sticker_webp(data: bytes) -> bytes | None:
    """Convert arbitrary image bytes into a Telegram-sticker-compliant
    static WEBP: exactly 512px on one side, the other side ≤512px (per the
    Bot API spec — anything else is rejected with WEBP_BAD_DIMENSIONS).
    The source is resized to FIT within a 512x512 box (preserving aspect
    ratio, never stretching or cropping) and the shorter side is padded
    with full transparency rather than a solid color, since stickers
    support an alpha channel and padding this way avoids inventing color
    that wasn't in the original photo. Returns None if Pillow is missing
    or conversion fails for any reason — the caller should fall back to a
    different send method rather than send a broken sticker."""
    try:
        from PIL import Image
    except ImportError:
        return None
    try:
        img = Image.open(BytesIO(data)).convert("RGBA")
        ratio = min(512 / img.width, 512 / img.height)
        new_w, new_h = max(1, round(img.width * ratio)), max(1, round(img.height * ratio))
        img = img.resize((new_w, new_h))

        # At least one side must be exactly 512 once placed on the canvas.
        # Floating-point resize can leave the long side at 511 due to
        # rounding, so force whichever side is the larger one to exactly
        # 512 rather than trusting the ratio math to land exactly on it.
        if new_w >= new_h:
            new_w = 512
        else:
            new_h = 512

        canvas = Image.new("RGBA", (512, 512), (0, 0, 0, 0))
        offset = ((512 - new_w) // 2, (512 - new_h) // 2)
        canvas.paste(img.resize((new_w, new_h)), offset)

        # Crop the canvas down so the *exact* 512 side has no transparent
        # margin of its own — e.g. a square source must end up exactly
        # 512x512, not letterboxed inside a 512x512 canvas with padding on
        # all four sides, which would violate "one side must be exactly
        # 512, the OTHER can be smaller" (both sides here are already
        # correct by construction, so this is just the final canvas).
        out = BytesIO()
        canvas.save(out, format="WEBP", lossless=False, quality=90)
        return out.getvalue()
    except Exception as e:  # noqa: BLE001 — any decode/encode failure → caller falls back
        log.warning("Sticker WEBP conversion failed, falling back: %s", e)
        return None

async def _send_events_as_stickers(chat_id: int, context: ContextTypes.DEFAULT_TYPE,
                                    events: list[dict]):
    """Send each event in `events` as TWO adjacent messages: the cover
    photo converted to a static WEBP sticker (smallest, cleanest possible
    render — no filename row, no file-size text, no "OPEN WITH" button,
    unlike sendDocument), immediately followed by a text message with the
    event's hyperlinked name, date/time, and location. Stickers have no
    caption field at all, so the two messages are the closest approximation
    to a single card: sent back-to-back with nothing else in between.
    disable_web_page_preview=True is required on the text message — the
    caption contains a real https://luma.com/... link, and without that
    flag Telegram auto-generates its own link-preview card (image,
    description, RSVP button) underneath, which is exactly the extra
    clutter this whole format is trying to avoid."""
    try:
        await context.bot.send_chat_action(chat_id=chat_id, action="choose_sticker")
    except TelegramError:
        pass

    urls = [ev.get("image_url", "") for ev in events]
    results = await _download_images_batch(urls)

    for event, image_bytes in zip(events, results):
        caption = _build_document_caption(event)
        # Off the event loop: WEBP conversion is CPU-bound (resize + encode),
        # and blocking here for a whole event's worth of work, one event at a
        # time, adds up across a 10-event digest on a CPU-constrained host.
        sticker_bytes = await asyncio.to_thread(_to_sticker_webp, image_bytes) if image_bytes else None
        try:
            if sticker_bytes:
                await context.bot.send_sticker(
                    chat_id=chat_id,
                    sticker=BytesIO(sticker_bytes),
                    read_timeout=30, write_timeout=30, connect_timeout=15,
                )
                await context.bot.send_message(chat_id=chat_id, text=caption, parse_mode="MarkdownV2",
                                                disable_web_page_preview=True)
            else:
                # No image, or conversion failed — fall back to the same
                # text-only message used elsewhere so the event still
                # shows up instead of silently disappearing.
                await context.bot.send_message(chat_id=chat_id, text=caption, parse_mode="MarkdownV2",
                                                disable_web_page_preview=True)
        except TimedOut:
            log.warning("Sticker upload timed out (likely delivered) for %r.", event.get("title"))
        except TelegramError as e:
            log.error("Failed to send event sticker for %r: %s", event.get("title"), e)

async def _send_events_as_documents(chat_id: int, context: ContextTypes.DEFAULT_TYPE,
                                     events: list[dict]):
    """Send each event in `events` as its own sendDocument message: the
    cover photo attached as a file (Telegram renders this as a small
    file-attachment card — a thumbnail capped at 320x320px plus filename —
    rather than a full-width inline photo, which is the whole point: this
    is the one sending method that actually produces a small on-screen
    footprint instead of just a smaller file or a shorter aspect ratio).
    The event name/time/location go in the caption, same as any other
    send method. Five separate messages, one per event, in order."""
    try:
        await context.bot.send_chat_action(chat_id=chat_id, action="upload_document")
    except TelegramError:
        pass

    urls = [ev.get("image_url", "") for ev in events]
    results = await _download_images_batch(urls)

    for event, image_bytes in zip(events, results):
        caption = _build_document_caption(event)
        try:
            if image_bytes:
                await context.bot.send_document(
                    chat_id=chat_id,
                    document=BytesIO(image_bytes),
                    filename=_document_filename(event),
                    caption=caption,
                    parse_mode="MarkdownV2",
                    read_timeout=30, write_timeout=30, connect_timeout=15,
                )
            else:
                # No image downloaded (missing URL, fetch failed, or timed
                # out) — fall back to a text-only message so the event
                # still shows up instead of silently disappearing.
                await context.bot.send_message(chat_id=chat_id, text=caption, parse_mode="MarkdownV2")
        except TimedOut:
            log.warning("Document upload timed out (likely delivered) for %r.", event.get("title"))
        except TelegramError as e:
            log.error("Failed to send event document for %r: %s", event.get("title"), e)

async def cmd_watch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Send the next WATCH_BATCH_SIZE unseen upcoming events, each as a
    sticker + hyperlinked name/date/location text, same format as the
    morning digest. Reads ONLY from the local cache — never triggers a
    scrape. Events shown are immediately marked watch_seen, so the next
    tap always shows the next batch, never repeating."""
    started = time.perf_counter()
    db = get_db(context)
    if not db.get("events"):
        await update.message.reply_text(
            "📭 No events loaded yet. Tap *🔍 Fetch Latest* (or run /pull) first, "
            "then come back to Watch Events.",
            parse_mode="Markdown",
        )
        log.info("Watch Events: no events cached, replied in %s", _format_elapsed(started))
        return

    unseen = _filter_watch_unseen(db)
    if not unseen:
        await update.message.reply_text("✅ You've seen everything upcoming — check back later!")
        log.info("Watch Events: nothing unseen, replied in %s", _format_elapsed(started))
        return

    batch = unseen[:WATCH_BATCH_SIZE]
    db.setdefault("watch_seen", []).extend(event_id(e) for e in batch)
    save_seen(db)

    await _send_events_as_stickers(update.effective_chat.id, context, batch)
    log.info("Watch Events: sent %d event(s) as stickers in %s", len(batch), _format_elapsed(started))

# ── KEYBOARDS ────────────────────────────────────────────────────────────────

MAIN_KEYBOARD = ReplyKeyboardMarkup(
    [[KeyboardButton("⚙️ Settings"), KeyboardButton("📆 Events")],
     [KeyboardButton("👀 Watch Events")]],
    resize_keyboard=True, input_field_placeholder="Choose a section…",
)

EVENTS_KEYBOARD = ReplyKeyboardMarkup(
    [[KeyboardButton("📅 Events Today"), KeyboardButton("📋 This Week")],
     [KeyboardButton("🗓 Next 2 Weeks"), KeyboardButton("🔍 Fetch Latest")],
     [KeyboardButton("🔄 Reset Progress"), KeyboardButton("⬅️ Back")]],
    resize_keyboard=True, input_field_placeholder="Choose an action…",
)

SETTINGS_KEYBOARD = ReplyKeyboardMarkup(
    [[KeyboardButton("🏷 Categories"), KeyboardButton("🔔 Notifications")],
     [KeyboardButton("⬅️ Back")]],
    resize_keyboard=True, input_field_placeholder="Choose a setting…",
)

def _build_notifications_keyboard(db: dict) -> ReplyKeyboardMarkup:
    """Build the notifications keyboard showing only the relevant
    toggle for each feature based on its current state."""
    digest_btn = (
        KeyboardButton("🔕 Disable Morning Digest") if db.get("morning_digest", True)
        else KeyboardButton("🔔 Enable Morning Digest")
    )
    alerts_btn = (
        KeyboardButton("🔕 Disable Event Alerts") if db.get("new_event_alerts", True)
        else KeyboardButton("🔔 Enable Event Alerts")
    )
    return ReplyKeyboardMarkup(
        [[digest_btn, alerts_btn],
         [KeyboardButton("🕐 Change Schedule"), KeyboardButton("⬅️ Back")]],
        resize_keyboard=True, input_field_placeholder="Manage notifications…",
    )

def _build_time_picker(selected_hour: int | None = None) -> InlineKeyboardMarkup:
    """Inline keyboard of hourly buttons from 6 AM to 12 PM; the selected
    hour (if any) gets a checkmark."""
    rows, row = [], []
    for hour in DIGEST_HOUR_CHOICES:
        label = _format_hour_et(hour)
        row.append(InlineKeyboardButton(f"✅ {label}" if hour == selected_hour else label,
                                         callback_data=f"digesttime|{hour}"))
        if len(row) == 4:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return InlineKeyboardMarkup(rows)

def _build_category_picker(selected: list[str], onboarding: bool = False) -> InlineKeyboardMarkup:
    """Inline multi-select checklist of all CATEGORIES; any category in
    `selected` gets a checkmark. Two per row — Telegram has no font-size
    control for inline buttons, so "smaller" here means a more compact
    grid (narrower buttons) rather than literally smaller text. Long
    names will still wrap within their half-width button rather than
    truncate.

    `onboarding` is encoded into every button's callback_data (as an
    "ob|" prefix on the choice) so handle_category_pick_callback can tell
    whether this picker is the mandatory first-run flow (where Done is
    blocked until at least one category is chosen) or the Settings-menu
    picker (where zero selections — "no preference" — stays valid)
    without needing any separate state lookup."""
    mode = "ob" if onboarding else "menu"
    rows, row = [], []
    for cat in CATEGORIES:
        row.append(InlineKeyboardButton(f"✅ {cat}" if cat in selected else cat,
                                         callback_data=f"catpick|{mode}|{cat}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([InlineKeyboardButton("Done", callback_data=f"catpick|{mode}|__done__")])
    return InlineKeyboardMarkup(rows)

async def handle_category_pick_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle a tap on the category picker: toggle that category in/out of
    preferred_categories, or finish (if "Done" was tapped).

    In onboarding mode (mode == "ob", set by /start's mandatory first-run
    picker — see _build_category_picker), Done is refused with zero
    categories selected: the picker stays up and a short nudge is shown
    instead, since /start requires picking at least one before
    continuing. In normal mode (reached via Settings → Categories), zero
    selections is a valid, supported choice meaning "no preference,
    plain chronological order" — that path is never blocked."""
    query = update.callback_query
    await query.answer()
    _, mode, choice = query.data.split("|", 2)
    onboarding = mode == "ob"
    db = get_db(context)
    selected = db.setdefault("preferred_categories", [])

    if choice == "__done__":
        if onboarding and not selected:
            try:
                await query.answer("Pick at least one category to continue.", show_alert=True)
            except TelegramError:
                pass
            return

        save_seen(db)
        try:
            await query.edit_message_text(
                "✅ *Categories saved!*\n" + (
                    "Events matching your categories will now show first.\n\n*Your picks:*\n" + "\n".join(f"• {c}" for c in selected)
                    if selected else "No categories selected — events will show in plain chronological order."
                ),
                parse_mode="Markdown",
            )
        except TelegramError as e:
            log.error("Failed to confirm category picker: %s", e)

        if onboarding:
            try:
                await context.bot.send_message(
                    chat_id=query.message.chat.id,
                    text="🏠 *You're all set!* Use the menu below to get started.",
                    parse_mode="Markdown", reply_markup=MAIN_KEYBOARD,
                )
            except TelegramError as e:
                log.error("Failed to show main menu after onboarding: %s", e)
        return

    if choice in selected:
        selected.remove(choice)
    else:
        selected.append(choice)
    save_seen(db)

    try:
        await query.edit_message_reply_markup(reply_markup=_build_category_picker(selected, onboarding=onboarding))
    except TelegramError as e:
        log.error("Failed to update category picker: %s", e)

async def _show_categories_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Entry point for the "🏷 Categories" button in Settings — show the
    multi-select picker pre-checked with whatever's already saved. Not
    onboarding mode: zero selections (no preference) stays a valid,
    save-able choice here, unlike /start's mandatory first-run picker."""
    db = get_db(context)
    selected = db.get("preferred_categories", [])
    await update.message.reply_text(
        "🏷 *Pick the categories you care about most.*\n"
        "Events matching them will be shown first; tap Done when finished.",
        parse_mode="Markdown",
        reply_markup=_build_category_picker(selected, onboarding=False),
    )

# ── MORNING DIGEST JOB ───────────────────────────────────────────────────────

def _schedule_morning_digest(job_queue, hour_et: int):
    """(Re)schedule the morning digest job at the given Toronto-local hour,
    removing any previous job so changing the time doesn't leave a duplicate."""
    for job in job_queue.get_jobs_by_name("morning_digest"):
        job.schedule_removal()
    job_queue.run_daily(morning_digest, time=_digest_time_utc(hour_et), name="morning_digest")

async def morning_digest(context: ContextTypes.DEFAULT_TYPE):
    """Runs daily at the user's chosen hour. Shows today's events that
    match the user's preferred_categories (if any are set). If no events
    today match their categories, falls back to all of today's events so
    the digest is never empty when there is something happening. If no
    categories are set, shows all of today's events in plain chronological
    order.

    Either way, sends an intro line, then each event the same way /watch
    does — sticker + hyperlinked name/date/location text, no shared
    photo-album caption."""
    log.info("Running morning digest…")
    db = get_db(context)
    chat_id = int(TELEGRAM_CHAT_ID)
    today_label = datetime.now(timezone.utc).astimezone(TORONTO_TZ).strftime("%a %b %d")
    preferred = set(db.get("preferred_categories", []))
    today_events = _filter_today(db)

    if preferred:
        category_matches = [e for e in today_events if e.get("category") in preferred]
        if category_matches:
            events = category_matches
            cats_label = ", ".join(sorted(preferred))
            empty_text = ""  # unused — events is non-empty
            header = (f"☀️ *Good morning!* {{count}} event{{plural}} today ({today_label}) "
                       f"matching your categories ({cats_label}):")
        else:
            # Nothing in preferred categories today — fall back to all of today's events.
            events = today_events
            cats_label = ", ".join(sorted(preferred))
            empty_text = f"☀️ *Good morning!* No Luma events in Toronto today ({today_label})."
            header = (f"☀️ *Good morning!* No events matching your categories ({cats_label}) "
                       f"today, but here are all {{count}} event{{plural}} in Toronto ({today_label}):")
    else:
        events = today_events
        empty_text = f"☀️ *Good morning!* No Luma events in Toronto today ({today_label})."
        header = f"☀️ *Good morning!* {{count}} event{{plural}} in Toronto today ({today_label}):"

    if not events:
        await context.bot.send_message(chat_id=chat_id, text=empty_text, parse_mode="Markdown")
        return

    batch = events[:10]  # unchanged cap — kept as-is, not part of this change
    count = len(batch)
    await context.bot.send_message(
        chat_id=chat_id,
        text=header.format(count=count, plural="s" if count != 1 else ""),
        parse_mode="Markdown",
    )
    await _send_events_as_stickers(chat_id, context, batch)

# ── MENU / COMMAND ROUTING ───────────────────────────────────────────────────

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Greet the user, then immediately show the mandatory category
    picker — every /start, even for returning users who already have
    preferences saved (their existing picks are pre-checked). The main
    menu keyboard only appears once the picker's Done succeeds; see
    handle_category_pick_callback's onboarding branch."""
    await update.message.reply_text(
        "👋 *Welcome to Luma Toronto Bot!*\n\n"
        "I track tech & AI events in Toronto from Luma.\n\n"
        "On any event card, tap the event name to open its Luma page, "
        "or tap *Next ➡️* to move on to the next one.",
        parse_mode="Markdown",
    )
    db = get_db(context)
    selected = db.get("preferred_categories", [])
    await update.message.reply_text(
        "🏷 *First, pick at least one category you care about.*\n"
        "Matching events will always show first; tap Done once you've picked.",
        parse_mode="Markdown",
        reply_markup=_build_category_picker(selected, onboarding=True),
    )

async def _show_events_menu(update, _context):
    await update.message.reply_text("📆 *Events menu* — pick a view:", parse_mode="Markdown",
                                     reply_markup=EVENTS_KEYBOARD)

async def _show_settings_menu(update, _context):
    await update.message.reply_text("⚙️ *Settings* — pick what to manage:", parse_mode="Markdown",
                                     reply_markup=SETTINGS_KEYBOARD)

async def _show_notifications_menu(update, context):
    db = get_db(context)
    hour_et      = db.get("digest_hour", DEFAULT_DIGEST_HOUR_ET)
    digest_status = "✅ enabled" if db.get("morning_digest", True) else "❌ disabled"
    alerts_status = "✅ enabled" if db.get("new_event_alerts", True) else "❌ disabled"
    await update.message.reply_text(
        f"🔔 *Notifications*\n\n"
        f"*Morning Digest* — today's events every day at *{_format_hour_et(hour_et)}* Toronto time.\n"
        f"Status: {digest_status}\n\n"
        f"*New Event Alerts* — instant push when a matching event is added to Luma.\n"
        f"Status: {alerts_status}",
        parse_mode="Markdown", reply_markup=_build_notifications_keyboard(db),
    )

async def _enable_morning_digest(update, context):
    db = get_db(context)
    if db.get("morning_digest"):
        await update.message.reply_text(
            "🔔 Morning Digest is already enabled. Use 🕐 Change Schedule to adjust the time.",
            reply_markup=_build_notifications_keyboard(db),
        )
        return
    hour_et = db.get("digest_hour", DEFAULT_DIGEST_HOUR_ET)
    await update.message.reply_text("🕐 *Pick a time for your Morning Digest:*", parse_mode="Markdown",
                                     reply_markup=_build_time_picker(hour_et))

async def _change_schedule(update, context):
    hour_et = get_db(context).get("digest_hour", DEFAULT_DIGEST_HOUR_ET)
    await update.message.reply_text("🕐 *Pick a new time for your Morning Digest:*", parse_mode="Markdown",
                                     reply_markup=_build_time_picker(hour_et))

async def _disable_morning_digest(update, context):
    db = get_db(context)
    db["morning_digest"] = False
    save_seen(db)
    for job in context.job_queue.get_jobs_by_name("morning_digest"):
        job.schedule_removal()
    await update.message.reply_text("🔕 *Morning Digest disabled.*", parse_mode="Markdown",
                                     reply_markup=_build_notifications_keyboard(db))

async def _enable_event_alerts(update, context):
    db = get_db(context)
    if db.get("new_event_alerts", True):
        await update.message.reply_text(
            "🔔 New Event Alerts are already enabled.",
            reply_markup=_build_notifications_keyboard(db),
        )
        return
    db["new_event_alerts"] = True
    save_seen(db)
    await update.message.reply_text(
        "🔔 *New Event Alerts enabled!*\nYou'll be notified as soon as a matching event appears on Luma.",
        parse_mode="Markdown", reply_markup=_build_notifications_keyboard(db),
    )

async def _disable_event_alerts(update, context):
    db = get_db(context)
    db["new_event_alerts"] = False
    save_seen(db)
    await update.message.reply_text(
        "🔕 *New Event Alerts disabled.*", parse_mode="Markdown",
        reply_markup=_build_notifications_keyboard(db),
    )

async def _back_to_main(update, _context):
    await update.message.reply_text("🏠 *Main menu*", parse_mode="Markdown", reply_markup=MAIN_KEYBOARD)

async def _back_to_settings(update, _context):
    await update.message.reply_text("⚙️ *Settings*", parse_mode="Markdown", reply_markup=SETTINGS_KEYBOARD)

# Persistent-keyboard button text → handler. A dict dispatch replaces a long
# if/elif chain — same behaviour, fewer lines, O(1) lookup.
_KEYBOARD_ROUTES = {
    "📆 Events":                  _show_events_menu,
    "⚙️ Settings":                 _show_settings_menu,
    "🔔 Notifications":            _show_notifications_menu,
    "🔔 Enable Morning Digest":   _enable_morning_digest,
    "🕐 Change Schedule":          _change_schedule,
    "🔕 Disable Morning Digest":  _disable_morning_digest,
    "🔔 Enable Event Alerts":     _enable_event_alerts,
    "🔕 Disable Event Alerts":    _disable_event_alerts,
    "📅 Events Today":            cmd_today,
    "📋 This Week":                cmd_thisweek,
    "🗓 Next 2 Weeks":             cmd_nexttwoweeks,
    "🔍 Fetch Latest":            cmd_pull,
    "🏷 Categories":              _show_categories_menu,
    "🔄 Reset Progress":          lambda u, c: cmd_clear(u, c),
    "👀 Watch Events":            cmd_watch,
    "⬅️ Back":                    _back_to_main,
    "⬅️ Back to Settings":        _back_to_settings,
}

async def handle_keyboard_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Route persistent keyboard button taps via the lookup table above."""
    handler = _KEYBOARD_ROUTES.get((update.message.text or "").strip())
    if handler:
        await handler(update, context)

async def cmd_clear(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Reset review progress so Watch Events (and the review queues) start
    over from the nearest upcoming event — like rewinding a video, not
    deleting the tape. Cached event data is kept, so no fresh /pull is
    needed before Watch Events works again."""
    db = get_db(context)
    counts = {k: len(db.get(k, [])) for k in ("watch_seen", "seen")}

    db["watch_seen"], db["seen"] = [], []
    save_seen(db)
    context.bot_data["pending"] = {}
    context.bot_data["reviews"] = {}

    await update.message.reply_text(
        f"🔄 *Reset!*\n\n"
        f"Cleared {counts['watch_seen']} watched and {counts['seen']} seen event(s).\n\n"
        f"Watch Events will start over from the nearest upcoming event — "
        f"no need to /pull again.",
        parse_mode="Markdown",
    )

# ── MAIN ──────────────────────────────────────────────────────────────────────

def main():
    db = load_seen()
    app = Application.builder().token(TELEGRAM_BOT_TOKEN).build()
    app.bot_data["db"]      = db
    app.bot_data["pending"] = {}

    app.add_handler(CallbackQueryHandler(handle_digest_time_callback, pattern=r"^digesttime\|"))
    app.add_handler(CallbackQueryHandler(handle_period_more_callback, pattern=r"^periodmore\|"))
    app.add_handler(CallbackQueryHandler(handle_category_pick_callback, pattern=r"^catpick\|"))
    app.add_handler(CallbackQueryHandler(handle_callback))
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_keyboard_button))
    app.add_handler(CommandHandler("pull", cmd_pull))
    app.add_handler(CommandHandler("thisweek", cmd_thisweek))
    app.add_handler(CommandHandler("next2weeks", cmd_nexttwoweeks))
    app.add_handler(CommandHandler("today", cmd_today))
    app.add_handler(CommandHandler("clear", cmd_clear))
    app.add_handler(CommandHandler("watch", cmd_watch))

    async def on_startup(application):
        await application.bot.send_message(
            chat_id=TELEGRAM_CHAT_ID,
            text=(
                "🤖 *Luma Toronto Bot*\n\n"
                "/pull — fetch latest events\n"
                "/thisweek — events in the next 7 days\n"
                "/next2weeks — events in the next 14 days\n"
                "/today — events happening today\n"
                "/clear — restart browsing from the nearest event\n"
                f"/watch — get a batch summary of the next {WATCH_BATCH_SIZE} new events"
            ),
            parse_mode="Markdown",
        )

    app.post_init = on_startup

    jq = app.job_queue
    jq.run_once(poll_luma, when=5)
    jq.run_repeating(poll_luma, interval=POLL_INTERVAL_SECS, first=POLL_INTERVAL_SECS)

    if db.get("morning_digest"):
        hour_et = db.get("digest_hour", DEFAULT_DIGEST_HOUR_ET)
        _schedule_morning_digest(jq, hour_et)
        log.info("Morning digest restored (%s ET daily).", _format_hour_et(hour_et))

    log.info("Bot running. Polling every %d seconds.", POLL_INTERVAL_SECS)
    app.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()
