"""
Persoonlijke assistent via Telegram, met Gemini als AI-model.

Veiligheid:
- Reageert alleen op het Telegram-account in ALLOWED_USER_ID.
- Alleen privechats; groepen worden genegeerd.
- De AI kan niets uitvoeren, alleen tekst terugsturen.
- Geheimen staan in /etc/assistent/assistent.env, niet in deze code.

Commando's:
  /herinner 10m thee        (m = minuten, u of h = uren, d = dagen)
  /herinner 14:30 bellen    (vandaag, of morgen als het tijdstip voorbij is)
  /herinner morgen 09:00 vuilnis
  /herinner 25-12 10:00 kerstcadeau
  /lijst, /verwijder 2, /reset, /help
"""

import json
import logging
import re
from collections import defaultdict, deque
from datetime import date, datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

from google import genai
from google.genai import types
from telegram import Update
from telegram.constants import ChatAction
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

CONFIG_PATH = Path("/etc/assistent/assistent.env")
DATA_DIR = Path("/opt/assistent/data")
REMINDERS_FILE = DATA_DIR / "herinneringen.json"
TZ = ZoneInfo("Europe/Amsterdam")
MAX_HISTORY = 20  # aantal berichten (vragen plus antwoorden) dat de bot onthoudt
TELEGRAM_LIMIT = 4000

SYSTEM_PROMPT = (
    "Je bent een persoonlijke assistent die via Telegram praat met je eigenaar. "
    "Antwoord in het Nederlands, tenzij de gebruiker een andere taal gebruikt. "
    "Wees kort en to the point. Gebruik geen tabellen of zware opmaak. "
    "Je kunt zelf geen acties uitvoeren, geen websites bezoeken en geen herinneringen zetten. "
    "Voor herinneringen verwijs je naar het commando /herinner, bijvoorbeeld "
    "'/herinner morgen 09:00 tandarts bellen'. "
    "Als je iets niet zeker weet, zeg dat eerlijk."
)

HELP_TEXT = (
    "Stel gewoon een vraag, dan antwoord ik.\n\n"
    "Herinneringen:\n"
    "/herinner 10m thee (m, u of d)\n"
    "/herinner 14:30 bellen\n"
    "/herinner morgen 09:00 vuilnis\n"
    "/herinner 25-12 10:00 cadeau\n"
    "/lijst: toon herinneringen\n"
    "/verwijder 2: verwijder nummer 2\n\n"
    "/reset: vergeet het gesprek tot nu toe"
)

logging.basicConfig(
    format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO
)
# httpx logt anders elke URL, en daar zit de bot-token in.
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("assistent")


# ---------- Configuratie ----------

def load_config(path: Path) -> dict:
    config = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        config[key.strip()] = value.strip().strip('"').strip("'")
    return config


CONFIG = load_config(CONFIG_PATH)
TELEGRAM_TOKEN = CONFIG["TELEGRAM_TOKEN"]
GEMINI_API_KEY = CONFIG["GEMINI_API_KEY"]
GEMINI_MODEL = CONFIG.get("GEMINI_MODEL") or "gemini-2.5-flash"
ALLOWED_USER_ID = int(CONFIG.get("ALLOWED_USER_ID") or 0)

gemini = genai.Client(api_key=GEMINI_API_KEY)
history = defaultdict(lambda: deque(maxlen=MAX_HISTORY))


# ---------- Toegang ----------

async def guard(update: Update) -> bool:
    """True als het bericht van de eigenaar komt, anders weigeren."""
    user = update.effective_user
    if ALLOWED_USER_ID and user and user.id == ALLOWED_USER_ID:
        return True
    uid = user.id if user else "onbekend"
    log.warning("Bericht geweigerd van user-id %s", uid)
    if not ALLOWED_USER_ID and update.effective_message:
        await update.effective_message.reply_text(
            f"Setup-modus. Jouw Telegram user-ID is: {uid}\n"
            "Zet dit getal bij ALLOWED_USER_ID in het configuratiebestand "
            "en start de bot opnieuw."
        )
    return False


# ---------- Hulpfuncties ----------

def split_message(text: str) -> list[str]:
    parts = []
    while len(text) > TELEGRAM_LIMIT:
        cut = text.rfind("\n", 0, TELEGRAM_LIMIT)
        if cut <= 0:
            cut = TELEGRAM_LIMIT
        parts.append(text[:cut])
        text = text[cut:].lstrip()
    parts.append(text)
    return parts


def fmt(dt: datetime) -> str:
    return dt.astimezone(TZ).strftime("%d-%m-%Y %H:%M")


# ---------- AI ----------

async def ask_gemini(chat_id: int, question: str) -> str:
    hist = history[chat_id]
    now = datetime.now(TZ).strftime("%Y-%m-%d %H:%M (%A)")
    user_msg = types.Content(role="user", parts=[types.Part(text=question)])
    response = await gemini.aio.models.generate_content(
        model=GEMINI_MODEL,
        contents=list(hist) + [user_msg],
        config=types.GenerateContentConfig(
            system_instruction=f"{SYSTEM_PROMPT} Huidige datum en tijd: {now}.",
        ),
    )
    answer = (response.text or "").strip() or "(Geen antwoord ontvangen.)"
    hist.append(user_msg)
    hist.append(types.Content(role="model", parts=[types.Part(text=answer)]))
    return answer


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard(update):
        return
    msg = update.effective_message
    await context.bot.send_chat_action(chat_id=msg.chat_id, action=ChatAction.TYPING)
    try:
        answer = await ask_gemini(msg.chat_id, msg.text)
    except Exception as exc:
        log.error("Fout bij Gemini: %s", exc)
        if "429" in str(exc) or "RESOURCE_EXHAUSTED" in str(exc):
            answer = (
                "De gratis limiet van Gemini is even bereikt. Probeer het over "
                "een minuut opnieuw, of morgen als de daglimiet op is."
            )
        else:
            answer = "Er ging iets mis bij het ophalen van een antwoord. Probeer het zo nog eens."
    for chunk in split_message(answer):
        await msg.reply_text(chunk)


async def on_other(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard(update):
        return
    await update.effective_message.reply_text("Ik kan voorlopig alleen tekst lezen.")


# ---------- Herinneringen ----------

REL = re.compile(r"^(\d+)(m|min|u|h|d)$", re.IGNORECASE)
TIME = re.compile(r"^(\d{1,2})[:.](\d{2})$")
DAY = re.compile(r"^(\d{1,2})-(\d{1,2})$")


def parse_when(args: list[str]):
    """Geeft (tijdstip, tekst) terug, of (None, '') als het niet te lezen is."""
    now = datetime.now(TZ)
    if not args:
        return None, ""
    first = args[0].lower()

    rel = REL.match(first)
    if rel:
        n, unit = int(rel.group(1)), rel.group(2).lower()
        if unit in ("m", "min"):
            delta = timedelta(minutes=n)
        elif unit in ("u", "h"):
            delta = timedelta(hours=n)
        else:
            delta = timedelta(days=n)
        return now + delta, " ".join(args[1:])

    day = None
    rest = args
    if first == "morgen":
        day, rest = (now + timedelta(days=1)).date(), args[1:]
    elif first == "overmorgen":
        day, rest = (now + timedelta(days=2)).date(), args[1:]
    elif DAY.match(first):
        d, m = map(int, DAY.match(first).groups())
        try:
            day = date(now.year, m, d)
            if day < now.date():
                day = date(now.year + 1, m, d)
        except ValueError:
            return None, ""
        rest = args[1:]

    if not rest:
        return None, ""
    t = TIME.match(rest[0])
    if not t:
        return None, ""
    hh, mm = int(t.group(1)), int(t.group(2))
    if hh > 23 or mm > 59:
        return None, ""

    if day is None:
        due = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
        if due <= now:
            due += timedelta(days=1)
    else:
        due = datetime(day.year, day.month, day.day, hh, mm, tzinfo=TZ)
    return due, " ".join(rest[1:])


def load_reminders() -> list[dict]:
    if not REMINDERS_FILE.exists():
        return []
    try:
        return json.loads(REMINDERS_FILE.read_text())
    except (json.JSONDecodeError, OSError):
        log.error("Kon herinneringen niet lezen; begin met een lege lijst.")
        return []


def save_reminders(reminders: list[dict]) -> None:
    tmp = REMINDERS_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(reminders, indent=2, ensure_ascii=False))
    tmp.replace(REMINDERS_FILE)


def remove_reminder(reminder_id: int) -> None:
    save_reminders([r for r in load_reminders() if r["id"] != reminder_id])


async def fire_reminder(context: ContextTypes.DEFAULT_TYPE) -> None:
    r = context.job.data
    prefix = "⏰ Gemiste herinnering" if r.get("missed") else "⏰ Herinnering"
    await context.bot.send_message(chat_id=r["chat_id"], text=f"{prefix}: {r['text']}")
    remove_reminder(r["id"])


def schedule(app: Application, r: dict, when) -> None:
    app.job_queue.run_once(fire_reminder, when=when, data=r, name=str(r["id"]))


async def cmd_herinner(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard(update):
        return
    due, text = parse_when(context.args)
    if due is None or not text.strip():
        await update.effective_message.reply_text(
            "Dat begreep ik niet. Voorbeelden:\n"
            "/herinner 10m thee\n/herinner 14:30 bellen\n"
            "/herinner morgen 09:00 vuilnis\n/herinner 25-12 10:00 cadeau"
        )
        return
    reminders = load_reminders()
    new_id = max((r["id"] for r in reminders), default=0) + 1
    r = {
        "id": new_id,
        "chat_id": update.effective_chat.id,
        "due": due.isoformat(),
        "text": text.strip(),
    }
    reminders.append(r)
    save_reminders(reminders)
    schedule(context.application, r, due)
    await update.effective_message.reply_text(f"Oké, ik herinner je op {fmt(due)}: {r['text']}")


def sorted_reminders() -> list[dict]:
    return sorted(load_reminders(), key=lambda r: r["due"])


async def cmd_lijst(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard(update):
        return
    items = sorted_reminders()
    if not items:
        await update.effective_message.reply_text("Geen herinneringen gepland.")
        return
    lines = [
        f"{i}. {fmt(datetime.fromisoformat(r['due']))}: {r['text']}"
        for i, r in enumerate(items, start=1)
    ]
    await update.effective_message.reply_text("\n".join(lines))


async def cmd_verwijder(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard(update):
        return
    items = sorted_reminders()
    try:
        r = items[int(context.args[0]) - 1]
    except (IndexError, ValueError):
        await update.effective_message.reply_text("Gebruik: /verwijder 2 (nummer uit /lijst)")
        return
    remove_reminder(r["id"])
    for job in context.job_queue.get_jobs_by_name(str(r["id"])):
        job.schedule_removal()
    await update.effective_message.reply_text(f"Verwijderd: {r['text']}")


async def cmd_reset(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard(update):
        return
    history.pop(update.effective_chat.id, None)
    await update.effective_message.reply_text("Gesprek gewist. We beginnen opnieuw.")


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard(update):
        return
    await update.effective_message.reply_text(HELP_TEXT)


async def restore_reminders(app: Application) -> None:
    """Na een herstart: geplande herinneringen opnieuw inplannen."""
    now = datetime.now(TZ)
    count = 0
    for r in load_reminders():
        due = datetime.fromisoformat(r["due"])
        if due <= now:
            r["missed"] = True
            schedule(app, r, 5)  # gemist tijdens uitval: over 5 seconden sturen
        else:
            schedule(app, r, due)
        count += 1
    log.info("%d herinnering(en) ingepland na opstarten.", count)


# ---------- Start ----------

def main() -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    app = ApplicationBuilder().token(TELEGRAM_TOKEN).post_init(restore_reminders).build()
    private = filters.ChatType.PRIVATE

    app.add_handler(CommandHandler(["start", "help"], cmd_help, filters=private))
    app.add_handler(CommandHandler("herinner", cmd_herinner, filters=private))
    app.add_handler(CommandHandler("lijst", cmd_lijst, filters=private))
    app.add_handler(CommandHandler("verwijder", cmd_verwijder, filters=private))
    app.add_handler(CommandHandler("reset", cmd_reset, filters=private))
    app.add_handler(MessageHandler(private & filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(private & ~filters.TEXT & ~filters.COMMAND, on_other))

    log.info(
        "Bot gestart met model %s. Toegestane user-id: %s",
        GEMINI_MODEL,
        ALLOWED_USER_ID or "nog niet ingesteld (setup-modus)",
    )
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
