import asyncio
import os
import re
import json
import logging
import time
import subprocess
import unicodedata
import uuid
from datetime import datetime, date, timedelta
from zoneinfo import ZoneInfo
from typing import Optional, Tuple
from io import BytesIO

import gspread
from google.oauth2.service_account import Credentials
from dotenv import load_dotenv
import google.generativeai as genai
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    CallbackQueryHandler,
    filters,
    ContextTypes,
)

load_dotenv(override=True)

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO
)
logger = logging.getLogger(__name__)

VN_TZ = ZoneInfo("Asia/Ho_Chi_Minh")

# --- Config ---
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
GOOGLE_SHEET_ID = os.getenv("GOOGLE_SHEET_ID")
GOOGLE_CREDENTIALS_JSON = os.getenv("GOOGLE_CREDENTIALS_JSON")
ALLOWED_USER_IDS = os.getenv("ALLOWED_USER_IDS", "")

GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.5-flash")

ALLOWED_USERS = set()
if ALLOWED_USER_IDS:
    for uid in ALLOWED_USER_IDS.split(","):
        uid = uid.strip()
        if not uid:
            continue
        try:
            ALLOWED_USERS.add(int(uid))
        except ValueError:
            logger.warning(f"Bỏ qua ALLOWED_USER_IDS không hợp lệ: {uid!r}")

# Initialize Gemini client for parsing, chat, and Vision OCR
genai.configure(api_key=GEMINI_API_KEY)
gemini_model = genai.GenerativeModel(GEMINI_MODEL)
logger.info(f"Gemini client ready (model={GEMINI_MODEL}).")

# --- Categories ---
EXPENSE_CATEGORIES = {
    "an": "CHI - Ăn uống",
    "anuong": "CHI - Ăn uống",
    "khac": "CHI - Khác",
    "muasam": "CHI - Mua sắm",
    "mua": "CHI - Mua sắm",
    "duahh": "CHI - Đưa HH",
    "hh": "CHI - Đưa HH",
    "saoke": "CHI - TT sao kê thẻ",
    "the": "CHI - TT sao kê thẻ",
    "luong": "CHI - Lương",
}

INCOME_CATEGORIES = {
    "luong": "THU - Lương",
    "khac": "THU - Khác",
    "thuong": "THU - Thưởng",
}

ALL_CHI_TYPES = [
    "CHI - Ăn uống",
    "CHI - Khác",
    "CHI - Mua sắm",
    "CHI - Đưa HH",
    "CHI - TT sao kê thẻ",
]

ALL_THU_TYPES = [
    "THU - Lương",
    "THU - Khác",
    "THU - Thưởng",
]

# --- Reminders storage (in-memory, lost on restart) ---
reminders_store: dict = {}  # {chat_id: [{"id": int, "time": datetime, "content": str, "job_name": str}]}
reminder_counter: int = 0

# --- Medication reminders ---
MEDICATION_HISTORY_FILE = "medication_history.json"
# medication -> (next_med_display, next_callback_key, delay_seconds) or None to end the chain
MEDICATION_CHAIN = {
    "Gaviscon": ("canxi", "canxi", 2 * 3600),
    "canxi": ("sắt", "sat", 2 * 3600),
    "sắt": None,  # handled by post-iron eat reminder, which then schedules vitamin
    "vitamin": ("canxi", "canxi", 2 * 3600),
}
MED_CALLBACK_MAP = {"canxi": "canxi", "sat": "sắt", "vitamin": "vitamin"}
MED_DELETE_WINDOW_SECONDS = 120  # 2 minutes to delete after saving
POST_IRON_EAT_REMINDER_MINUTES = 30  # remind to eat 30 min after taking iron
POST_EAT_VITAMIN_REMINDER_MINUTES = 30  # remind to take vitamin 30 min after the eat reminder

# Pending confirmations waiting for Lưu lại / Huỷ (in-memory)
pending_med_confirmations: dict = {}  # {token: {"medication", "chat_id", "user_id"}}


def get_sheet():
    """Connect to Google Sheet and return the worksheet."""
    scopes = [
        "https://www.googleapis.com/auth/spreadsheets",
        "https://www.googleapis.com/auth/drive",
    ]
    if not GOOGLE_CREDENTIALS_JSON:
        raise RuntimeError("GOOGLE_CREDENTIALS_JSON env var is not set")
    creds_info = json.loads(GOOGLE_CREDENTIALS_JSON)
    creds = Credentials.from_service_account_info(creds_info, scopes=scopes)
    client = gspread.authorize(creds)
    spreadsheet = client.open_by_key(GOOGLE_SHEET_ID)
    year = datetime.now(VN_TZ).year
    sheet_name = f"Năm {year}"
    try:
        worksheet = spreadsheet.worksheet(sheet_name)
    except gspread.WorksheetNotFound:
        worksheet = spreadsheet.sheet1
    return worksheet


def parse_amount(text: str) -> Optional[int]:
    """Parse amount from text like '150k', '1.5tr', '1,500,000', '150000'."""
    text = text.strip().lower().replace(",", "").replace(".", "")

    original = text
    match = re.match(r"^([\d.,]+)\s*(k|tr|trieu|triệu|m|nghìn|nghin)?$", original.replace(",", "."))
    if match:
        num_str = match.group(1).replace(",", ".")
        suffix = match.group(2) or ""
        try:
            num = float(num_str)
        except ValueError:
            return None

        if suffix in ("k", "nghìn", "nghin"):
            return int(num * 1_000)
        elif suffix in ("tr", "trieu", "triệu", "m"):
            return int(num * 1_000_000)
        else:
            return int(num)

    return None


def parse_date(text: str) -> Optional[str]:
    """Parse date from text. Returns DD/MM/YY format."""
    text = text.strip().lower()
    today = date.today()

    if text in ("hn", "homnay", "hômnay", "hom nay", "hôm nay", "today", ""):
        return today.strftime("%d/%m/%y")
    if text in ("hq", "homqua", "hômqua", "hom qua", "hôm qua", "yesterday"):
        return (today - timedelta(days=1)).strftime("%d/%m/%y")

    for fmt in ("%d/%m/%Y", "%d/%m/%y", "%d/%m", "%d-%m-%Y", "%d-%m-%y", "%d-%m"):
        try:
            parsed = datetime.strptime(text, fmt)
            if "%Y" not in fmt and "%y" not in fmt:
                parsed = parsed.replace(year=today.year)
            return parsed.strftime("%d/%m/%y")
        except ValueError:
            continue

    return None


def parse_message(text: str) -> Optional[dict]:
    """
    Parse natural language expense/income message.

    Supported formats:
        chi 150k bún đậu
        thu 5tr lương tháng 3
        chi an 140k bún đậu 04/03
        chi mua 408k quần áo 16/03
        chi 2tr đưa hh 10/03
        thu luong 15tr
    """
    text = text.strip()
    if not text:
        return None

    lower = text.lower()
    is_income = None
    if lower.startswith("thu "):
        is_income = True
        text = text[4:].strip()
    elif lower.startswith("chi "):
        is_income = False
        text = text[4:].strip()
    else:
        return None

    category = None
    lower_remaining = text.lower()
    cat_map = INCOME_CATEGORIES if is_income else EXPENSE_CATEGORIES

    for key, val in sorted(cat_map.items(), key=lambda x: -len(x[0])):
        if lower_remaining.startswith(key + " "):
            category = val
            text = text[len(key):].strip()
            break

    amount = None
    amount_match = re.search(r"([\d.,]+\s*(?:k|tr|trieu|triệu|m|nghìn|nghin)?)\b", text, re.IGNORECASE)
    if amount_match:
        amount = parse_amount(amount_match.group(1))
        text = text[:amount_match.start()] + text[amount_match.end():]
        text = text.strip()

    if amount is None:
        return None

    transaction_date = None
    date_match = re.search(r"\b(\d{1,2}[/-]\d{1,2}(?:[/-]\d{2,4})?)\b", text)
    if date_match:
        transaction_date = parse_date(date_match.group(1))
        text = text[:date_match.start()] + text[date_match.end():]
        text = text.strip()

    for kw in ("hôm nay", "hom nay", "homnay", "hn", "hôm qua", "hom qua", "homqua", "hq"):
        if kw in text.lower():
            transaction_date = parse_date(kw)
            text = re.sub(re.escape(kw), "", text, flags=re.IGNORECASE).strip()
            break

    if transaction_date is None:
        transaction_date = date.today().strftime("%d/%m/%y")

    description = re.sub(r"\s+", " ", text).strip()

    if category is None:
        # 1) Look up history from Google Sheet
        category = guess_category_from_history(description, is_income)

        # 2) Fallback: simple rules
        if category is None:
            desc_lower = description.lower()
            if is_income:
                if any(w in desc_lower for w in ("lương", "luong", "salary")):
                    category = "THU - Lương"
                elif any(w in desc_lower for w in ("thưởng", "thuong", "bonus")):
                    category = "THU - Thưởng"
                else:
                    category = "THU - Khác"
            else:
                if any(w in desc_lower for w in ("ăn", "uống", "an ", "uong")):
                    category = "CHI - Ăn uống"
                else:
                    category = "CHI - Khác"

    month = datetime.strptime(transaction_date, "%d/%m/%y").month

    return {
        "is_income": is_income,
        "category": category,
        "description": description,
        "amount": amount,
        "date": transaction_date,
        "month": month,
    }


def find_insert_row(worksheet, month: int) -> int:
    """Find the correct row to insert data for the given month."""
    all_values = worksheet.get_all_values()

    month_header_rows = {}
    for i, row in enumerate(all_values):
        for cell in row:
            match = re.match(r"THÁNG\s+(\d+)", str(cell).strip())
            if match:
                month_header_rows[int(match.group(1))] = i + 1

    if month in month_header_rows:
        next_month_row = None
        for m in range(month + 1, 13):
            if m in month_header_rows:
                next_month_row = month_header_rows[m]
                break

        if next_month_row:
            start = month_header_rows[month]
            insert_at = start + 1
            for i in range(start, next_month_row - 1):
                if i < len(all_values) and any(all_values[i]):
                    insert_at = i + 2
            return insert_at
        else:
            start = month_header_rows[month]
            insert_at = start + 1
            for i in range(start, len(all_values)):
                if any(all_values[i]):
                    insert_at = i + 2
            return insert_at
    else:
        return len(all_values) + 1


def add_to_sheet(data: dict) -> Tuple[str, int]:
    """Add a transaction to Google Sheet. Returns (confirmation message, row_num)."""
    worksheet = get_sheet()

    row_num = find_insert_row(worksheet, data["month"])

    thu_amount = data["amount"] if data["is_income"] else ""
    chi_amount = data["amount"] if not data["is_income"] else ""

    row = [
        data["month"],
        data["category"],
        data["description"],
        thu_amount,
        chi_amount,
        data["date"],
        data.get("note", ""),
    ]

    worksheet.insert_row(row, row_num, value_input_option="USER_ENTERED")

    type_str = "Thu" if data["is_income"] else "Chi"
    amount_fmt = f"{data['amount']:,.0f}".replace(",", ".")
    msg = (
        f"Thưa Chủ nhân, em đã ghi nhận ạ!\n"
        f"  {type_str}: {amount_fmt} VND\n"
        f"  Loại: {data['category']}\n"
        f"  Nội dung: {data['description']}\n"
        f"  Ngày: {data['date']}\n"
        f"  Dòng: {row_num}"
    )
    return msg, row_num


def get_row_data(worksheet, row_num: int) -> Optional[dict]:
    """Get data from a specific row."""
    try:
        row = worksheet.row_values(row_num)
        if not row or len(row) < 6:
            return None
        return {
            "month": row[0],
            "category": row[1] if len(row) > 1 else "",
            "description": row[2] if len(row) > 2 else "",
            "thu": row[3] if len(row) > 3 else "",
            "chi": row[4] if len(row) > 4 else "",
            "date": row[5] if len(row) > 5 else "",
        }
    except Exception:
        return None


def delete_from_sheet(row_num: int) -> str:
    """Delete a row from the sheet."""
    worksheet = get_sheet()
    row_data = get_row_data(worksheet, row_num)
    if not row_data:
        return "Thưa Chủ nhân, em không tìm thấy dòng này ạ."

    desc = row_data["description"]
    amount = row_data["chi"] if row_data["chi"] else row_data["thu"]
    worksheet.delete_rows(row_num)
    amount_str = f"{safe_int(amount):,.0f}".replace(",", ".") if amount else "?"
    return f"Thưa Chủ nhân, em đã xoá thành công ạ: {desc} - {amount_str} VND (dòng {row_num})"


def update_category_in_sheet(row_num: int, new_category: str) -> str:
    """Update category of a row in the sheet."""
    worksheet = get_sheet()
    row_data = get_row_data(worksheet, row_num)
    if not row_data:
        return "Thưa Chủ nhân, em không tìm thấy dòng này ạ."
    old_category = row_data["category"]
    worksheet.update_cell(row_num, 2, new_category)
    # Invalidate cache so next lookup picks up the change
    _category_cache["last_refresh"] = 0
    return (
        f"Thưa Chủ nhân, em đã sửa loại thành công ạ!\n"
        f"  {old_category} -> {new_category}\n"
        f"  Nội dung: {row_data['description']}\n"
        f"  Dòng: {row_num}"
    )


# --- Category history cache ---
_category_cache = {"data": {}, "last_refresh": 0}
CACHE_TTL = 600  # 10 minutes


def learn_categories_from_sheet() -> dict:
    """Read sheet history and build description->category mapping. Cached 10 min."""
    now = time.time()
    if now - _category_cache["last_refresh"] < CACHE_TTL and _category_cache["data"]:
        return _category_cache["data"]

    try:
        worksheet = get_sheet()
        all_rows = worksheet.get_all_values()
        mapping = {}  # description_lower -> category
        for row in all_rows:
            if len(row) < 3:
                continue
            category = row[1].strip()
            description = row[2].strip()
            if not category or not description:
                continue
            if not category.startswith(("CHI", "THU")):
                continue
            mapping[description.lower()] = category
        _category_cache["data"] = mapping
        _category_cache["last_refresh"] = now
        logger.info(f"Loaded {len(mapping)} category mappings from sheet.")
        return mapping
    except Exception as e:
        logger.error(f"Error loading category history: {e}")
        return _category_cache["data"]


def guess_category_from_history(description: str, is_income: bool) -> Optional[str]:
    """Guess category based on sheet history. Returns None if no match."""
    mapping = learn_categories_from_sheet()
    desc_lower = description.lower().strip()
    prefix = "THU" if is_income else "CHI"

    # Exact match
    if desc_lower in mapping and mapping[desc_lower].startswith(prefix):
        return mapping[desc_lower]

    # Fuzzy: find history entries where description contains or is contained by input
    best_match = None
    best_len = 0
    for hist_desc, hist_cat in mapping.items():
        if not hist_cat.startswith(prefix):
            continue
        if hist_desc in desc_lower or desc_lower in hist_desc:
            if len(hist_desc) > best_len:
                best_match = hist_cat
                best_len = len(hist_desc)

    return best_match


async def parse_reminder_with_gemini(text: str) -> Optional[dict]:
    """Use Gemini to parse a Vietnamese reminder request into structured data."""
    try:
        now = datetime.now(VN_TZ)
        system_prompt = (
            "Bạn là parser nhắc nhở. Trích xuất thời gian và nội dung từ tin nhắn tiếng Việt.\n"
            f"Thời gian hiện tại: {now.strftime('%Y-%m-%d %H:%M')} (ngày {now.strftime('%d/%m/%Y')}, "
            f"{'thứ ' + str(now.isoweekday())} trong tuần).\n"
            "Trả về JSON duy nhất: {\"hour\": <0-23>, \"minute\": <0-59>, \"date\": \"YYYY-MM-DD\", \"content\": \"<nội dung nhắc>\"}\n"
            "Quy tắc:\n"
            "- 'chiều' = +12h (3h chiều = 15:00)\n"
            "- 'tối' = buổi tối (8h tối = 20:00)\n"
            "- 'sáng mai' = ngày mai buổi sáng\n"
            "- 'X phút nữa' hoặc 'X tiếng nữa' = tính từ thời gian hiện tại\n"
            "- Nếu không nói ngày, mặc định là hôm nay. Nếu giờ đã qua thì là ngày mai.\n"
            "- content là phần nội dung cần nhắc (bỏ phần 'nhắc tôi', 'nhắc', thời gian)\n"
            "Chỉ trả về JSON, không giải thích."
        )
        response = await asyncio.to_thread(
            gemini_model.generate_content,
            [system_prompt, text],
            generation_config={"max_output_tokens": 256, "temperature": 0.0},
        )
        response_text = response.text.strip()
        logger.info(f"Reminder parse response: {response_text}")
        json_match = re.search(r'\{[^}]+\}', response_text)
        if json_match:
            return json.loads(json_match.group())
        return None
    except Exception as e:
        logger.error(f"Reminder parse error: {e}")
        return None


async def send_reminder(context: ContextTypes.DEFAULT_TYPE) -> None:
    """JobQueue callback - send reminder message when due."""
    job = context.job
    chat_id = job.chat_id
    data = job.data

    await context.bot.send_message(
        chat_id=chat_id,
        text=(
            f"🔔 Thưa Chủ nhân, em xin nhắc Chủ nhân ạ:\n\n"
            f"  {data['content']}\n\n"
            f"  (Đặt lúc: {data['set_time']})"
        ),
    )

    # Remove from store
    if chat_id in reminders_store:
        reminders_store[chat_id] = [
            r for r in reminders_store[chat_id] if r["job_name"] != job.name
        ]


async def handle_reminder_request(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str) -> None:
    """Parse and schedule a reminder from natural language."""
    global reminder_counter

    await update.message.reply_text("Thưa Chủ nhân, em đang xử lý nhắc nhở ạ...")

    parsed = await parse_reminder_with_gemini(text)
    if not parsed or "hour" not in parsed or "content" not in parsed:
        await update.message.reply_text(
            "Thưa Chủ nhân, em không hiểu thời gian nhắc nhở ạ.\n"
            "Chủ nhân xinh đẹp vui lòng thử lại, ví dụ:\n"
            "  nhắc tôi 3h chiều họp team\n"
            "  nhắc 5 phút nữa uống nước\n"
            "  nhắc 8h sáng mai đi khám bệnh"
        )
        return

    # Build target datetime
    try:
        target_date = parsed.get("date")
        if target_date:
            target = datetime.strptime(target_date, "%Y-%m-%d").replace(
                hour=parsed["hour"], minute=parsed.get("minute", 0), tzinfo=VN_TZ
            )
        else:
            target = datetime.now(VN_TZ).replace(
                hour=parsed["hour"], minute=parsed.get("minute", 0), second=0, microsecond=0
            )

        now = datetime.now(VN_TZ)
        if target <= now:
            target += timedelta(days=1)

        delay = (target - now).total_seconds()
        if delay <= 0:
            await update.message.reply_text("Thưa Chủ nhân, thời gian này đã qua rồi ạ.")
            return

        reminder_counter += 1
        job_name = f"reminder_{update.effective_chat.id}_{reminder_counter}"
        chat_id = update.effective_chat.id

        job_data = {
            "content": parsed["content"],
            "set_time": now.strftime("%H:%M %d/%m"),
        }

        context.job_queue.run_once(
            send_reminder,
            when=delay,
            data=job_data,
            name=job_name,
            chat_id=chat_id,
        )

        # Store reminder
        if chat_id not in reminders_store:
            reminders_store[chat_id] = []
        reminders_store[chat_id].append({
            "id": reminder_counter,
            "time": target,
            "content": parsed["content"],
            "job_name": job_name,
        })

        await update.message.reply_text(
            f"Thưa Chủ nhân, em đã đặt nhắc nhở ạ!\n\n"
            f"  Thời gian: {target.strftime('%H:%M ngày %d/%m/%Y')}\n"
            f"  Nội dung: {parsed['content']}\n"
            f"  ID: #{reminder_counter}"
        )
    except Exception as e:
        logger.error(f"Reminder scheduling error: {e}")
        await update.message.reply_text(f"Thưa Chủ nhân, em gặp lỗi khi đặt nhắc nhở ạ: {e}")


def load_medication_history() -> dict:
    """Load medication history from JSON file."""
    try:
        with open(MEDICATION_HISTORY_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_medication_history(data: dict) -> None:
    """Save medication history to JSON file."""
    with open(MEDICATION_HISTORY_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def log_medication(
    user_id: int,
    medication: str,
    taken_at: Optional[datetime] = None,
    next_job_name: Optional[str] = None,
    eat_job_name: Optional[str] = None,
) -> dict:
    """Append medication entry to history. Returns the stored entry."""
    history = load_medication_history()
    key = str(user_id)
    if key not in history:
        history[key] = []
    if taken_at is None:
        taken_at = datetime.now(VN_TZ)
    entry = {
        "id": uuid.uuid4().hex[:10],
        "timestamp": taken_at.isoformat(),
        "date": taken_at.strftime("%Y-%m-%d"),
        "time": taken_at.strftime("%H:%M"),
        "medication": medication,
        "next_job_name": next_job_name,
        "eat_job_name": eat_job_name,
    }
    history[key].append(entry)
    save_medication_history(history)
    return entry


def find_medication_entry(user_id: int, entry_id: str) -> Optional[dict]:
    history = load_medication_history()
    for item in history.get(str(user_id), []):
        if item.get("id") == entry_id:
            return item
    return None


def delete_medication_entry(user_id: int, entry_id: str) -> Optional[dict]:
    history = load_medication_history()
    key = str(user_id)
    items = history.get(key, [])
    for i, item in enumerate(items):
        if item.get("id") == entry_id:
            removed = items.pop(i)
            save_medication_history(history)
            return removed
    return None


def count_medication_today(user_id: int, medication: str, on_date: str) -> int:
    """Count how many `medication` entries the user logged on `on_date` (YYYY-MM-DD)."""
    history = load_medication_history()
    return sum(
        1
        for item in history.get(str(user_id), [])
        if item.get("medication") == medication and item.get("date") == on_date
    )


async def send_medication_reminder(context: ContextTypes.DEFAULT_TYPE) -> None:
    """JobQueue callback - remind user to take next medication with a button."""
    job = context.job
    next_med = job.data["next_medication"]
    next_key = job.data["next_key"]

    keyboard = InlineKeyboardMarkup([[
        InlineKeyboardButton(f"Đã uống {next_med}", callback_data=f"med_{next_key}")
    ]])
    await context.bot.send_message(
        chat_id=job.chat_id,
        text=f"💊 Thưa Chủ nhân, đã đến giờ uống {next_med} ạ!",
        reply_markup=keyboard,
    )


def schedule_next_medication(
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int,
    current_med: str,
    taken_at: datetime,
    user_id: int,
) -> Optional[Tuple[str, datetime, str]]:
    """Schedule next medication reminder anchored at taken_at + chain delay.

    Returns (next_med, reminder_time, job_name) or None.
    """
    chain = MEDICATION_CHAIN.get(current_med)
    if not chain:
        return None
    # Canxi is taken twice a day: the 1st dose chains to sắt, the 2nd dose
    # (after vitamin) completes the day. This entry isn't logged yet, so a
    # prior canxi today means the one being saved now is the 2nd.
    if current_med == "canxi" and count_medication_today(
        user_id, "canxi", taken_at.strftime("%Y-%m-%d")
    ) >= 1:
        return None
    next_med, next_key, delay_seconds = chain

    now = datetime.now(VN_TZ)
    reminder_time = taken_at + timedelta(seconds=delay_seconds)
    actual_delay = max(1.0, (reminder_time - now).total_seconds())
    job_name = f"medreminder_{chat_id}_{uuid.uuid4().hex[:8]}"

    context.job_queue.run_once(
        send_medication_reminder,
        when=actual_delay,
        data={"next_medication": next_med, "next_key": next_key},
        name=job_name,
        chat_id=chat_id,
    )
    return next_med, reminder_time, job_name


async def send_eat_reminder(context: ContextTypes.DEFAULT_TYPE) -> None:
    """JobQueue callback - remind user to eat 30 min after taking iron, then schedule vitamin."""
    job = context.job
    chat_id = job.chat_id
    await context.bot.send_message(
        chat_id=chat_id,
        text=(
            f"🍚 Thưa Chủ nhân, đã {POST_IRON_EAT_REMINDER_MINUTES} phút kể từ khi uống sắt rồi ạ. "
            f"Chủ nhân đi ăn thôi!"
        ),
    )

    # Chain: 30 minutes after the eat reminder, remind to take vitamin.
    vitamin_job_name = f"medreminder_{chat_id}_{uuid.uuid4().hex[:8]}"
    context.job_queue.run_once(
        send_medication_reminder,
        when=POST_EAT_VITAMIN_REMINDER_MINUTES * 60,
        data={"next_medication": "vitamin", "next_key": "vitamin"},
        name=vitamin_job_name,
        chat_id=chat_id,
    )


def schedule_post_iron_eat_reminder(
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int,
    taken_at: datetime,
) -> Tuple[datetime, str]:
    """Schedule an eat reminder 30 min after iron. Returns (reminder_time, job_name)."""
    now = datetime.now(VN_TZ)
    reminder_time = taken_at + timedelta(minutes=POST_IRON_EAT_REMINDER_MINUTES)
    actual_delay = max(1.0, (reminder_time - now).total_seconds())
    job_name = f"eatreminder_{chat_id}_{uuid.uuid4().hex[:8]}"
    context.job_queue.run_once(
        send_eat_reminder,
        when=actual_delay,
        name=job_name,
        chat_id=chat_id,
    )
    return reminder_time, job_name


async def remove_delete_button(context: ContextTypes.DEFAULT_TYPE) -> None:
    """JobQueue callback - remove the Xoá button after the delete window expires."""
    job = context.job
    try:
        await context.bot.edit_message_reply_markup(
            chat_id=job.data["chat_id"],
            message_id=job.data["message_id"],
            reply_markup=None,
        )
    except Exception as e:
        logger.info(f"remove_delete_button skipped: {e}")


async def show_medication_confirmation(
    target,
    context: ContextTypes.DEFAULT_TYPE,
    medication: str,
    is_query: bool,
    taken_at: Optional[datetime] = None,
) -> None:
    """Show 'Lưu lại / Huỷ' confirmation for a medication.

    `taken_at` defaults to now; pass an earlier datetime when the user
    reports the time they took the med (e.g. "đã uống Gaviscon lúc 12:19").
    """
    token = uuid.uuid4().hex[:10]
    if is_query:
        chat_id = target.message.chat_id
        user_id = target.from_user.id
    else:
        chat_id = target.chat_id
        user_id = target.from_user.id

    if taken_at is None:
        taken_at = datetime.now(VN_TZ)

    pending_med_confirmations[token] = {
        "medication": medication,
        "chat_id": chat_id,
        "user_id": user_id,
        "taken_at": taken_at,
    }

    text = (
        f"Thưa Chủ nhân, em xin xác nhận ạ:\n\n"
        f"  💊 Uống {medication}\n"
        f"  Thời gian: {taken_at.strftime('%H:%M %d/%m/%Y')}\n\n"
        f"Chủ nhân có muốn em lưu vào lịch sử không ạ?"
    )
    keyboard = InlineKeyboardMarkup([[
        InlineKeyboardButton("Lưu lại", callback_data=f"medsave_{token}"),
        InlineKeyboardButton("Huỷ", callback_data=f"medskip_{token}"),
    ]])

    if is_query:
        await target.edit_message_text(text, reply_markup=keyboard)
    else:
        await target.reply_text(text, reply_markup=keyboard)


def extract_time_from_text(text: str) -> Optional[Tuple[int, int]]:
    """Extract a 24-hour clock time from free text.

    Recognises 12:19, 12h19, 12g19, 12 giờ 19, 12h, 12g, 12 giờ, 12:00.
    Returns (hour, minute) or None.
    """
    patterns_hm = [
        r'(?<!\d)(\d{1,2})\s*[:hg]\s*(\d{2})(?!\d)',
        r'(?<!\d)(\d{1,2})\s*(?:giờ|gio)\s*(\d{1,2})(?!\d)',
    ]
    for pat in patterns_hm:
        m = re.search(pat, text)
        if m:
            h, mn = int(m.group(1)), int(m.group(2))
            if 0 <= h < 24 and 0 <= mn < 60:
                return h, mn
    patterns_h = [
        r'(?<!\d)(\d{1,2})\s*[hg](?!\d|[a-zA-ZÀ-ỹ])',
        r'(?<!\d)(\d{1,2})\s*(?:giờ|gio)\b',
    ]
    for pat in patterns_h:
        m = re.search(pat, text)
        if m:
            h = int(m.group(1))
            if 0 <= h < 24:
                return h, 0
    return None


def parse_medication_taken_text(text: str) -> Optional[dict]:
    """Detect 'đã uống <med>' / 'da uong <med>' with optional clock time.

    Returns {"medication": str, "time": Optional[(h, m)]} or None.
    """
    normalized = unicodedata.normalize("NFC", text.lower())
    if "đã uống" not in normalized and "da uong" not in normalized:
        return None
    if re.search(r'\bgaviscon\b', normalized):
        medication = "Gaviscon"
    elif re.search(r'\bcanxi\b', normalized):
        medication = "canxi"
    elif re.search(r'\bsắt\b', normalized) or re.search(r'\bsat\b', normalized):
        medication = "sắt"
    elif re.search(r'\bvitamin\b', normalized):
        medication = "vitamin"
    else:
        return None
    return {"medication": medication, "time": extract_time_from_text(normalized)}


def parse_med_reminder_request(text: str) -> Optional[dict]:
    """Parse 'nhắc uống sắt/vitamin trong X phút/tiếng' into {medication, key, delay_seconds}."""
    normalized = unicodedata.normalize("NFC", text.lower())

    if "nhắc" not in normalized and "nhac" not in normalized:
        return None

    if "uống sắt" in normalized or "uong sat" in normalized:
        medication, med_key = "sắt", "sat"
    elif "uống vitamin" in normalized or "uong vitamin" in normalized:
        medication, med_key = "vitamin", "vitamin"
    else:
        return None

    m = re.search(r'(\d+)\s*(phút|phut|tiếng|tieng|giờ|gio|p|h)\b', normalized)
    if not m:
        return None

    # Avoid matching absolute times like "3h chiều", "8 giờ sáng"
    after = normalized[m.end():].lstrip()
    if after[:6].startswith(("chiều", "chieu", "sáng", "sang", "tối", "toi", "trưa", "trua")):
        return None

    num = int(m.group(1))
    unit = m.group(2)
    delay_seconds = num * 60 if unit in ("phút", "phut", "p") else num * 3600
    if delay_seconds <= 0:
        return None

    return {"medication": medication, "med_key": med_key, "delay_seconds": delay_seconds}


async def handle_med_reminder_schedule(update: Update, context: ContextTypes.DEFAULT_TYPE, parsed: dict) -> None:
    """Schedule a manual medication reminder (for when user forgot the chain)."""
    chat_id = update.effective_chat.id
    medication = parsed["medication"]
    med_key = parsed["med_key"]
    delay = parsed["delay_seconds"]

    now = datetime.now(VN_TZ)
    reminder_time = now + timedelta(seconds=delay)
    job_name = f"medreminder_{chat_id}_{uuid.uuid4().hex[:8]}"

    context.job_queue.run_once(
        send_medication_reminder,
        when=delay,
        data={"next_medication": medication, "next_key": med_key},
        name=job_name,
        chat_id=chat_id,
    )

    if delay >= 3600:
        hours, rem = divmod(delay, 3600)
        mins = rem // 60
        time_str = f"{hours} tiếng" + (f" {mins} phút" if mins else "")
    else:
        time_str = f"{delay // 60} phút"

    await update.message.reply_text(
        f"Thưa Chủ nhân, em đã đặt nhắc uống {medication} sau {time_str} nữa ạ.\n"
        f"Thời gian: {reminder_time.strftime('%H:%M ngày %d/%m/%Y')}"
    )


async def _medication_save(query, context: ContextTypes.DEFAULT_TYPE) -> None:
    token = query.data.replace("medsave_", "")
    pending = pending_med_confirmations.pop(token, None)
    if not pending:
        await query.edit_message_text("Thưa Chủ nhân, xác nhận này đã hết hạn ạ.")
        return

    medication = pending["medication"]
    chat_id = pending["chat_id"]
    user_id = pending["user_id"]
    taken_at = pending.get("taken_at") or datetime.now(VN_TZ)

    next_job_name = None
    eat_job_name = None
    next_lines = []

    if medication == "sắt":
        eat_reminder_time, eat_job_name = schedule_post_iron_eat_reminder(context, chat_id, taken_at)
        vitamin_time = eat_reminder_time + timedelta(minutes=POST_EAT_VITAMIN_REMINDER_MINUTES)
        next_lines.append(
            f"Em sẽ nhắc Chủ nhân đi ăn lúc {eat_reminder_time.strftime('%H:%M')} "
            f"(sau {POST_IRON_EAT_REMINDER_MINUTES} phút) ạ."
        )
        next_lines.append(
            f"Sau đó em sẽ nhắc uống vitamin lúc {vitamin_time.strftime('%H:%M')} ạ."
        )
    else:
        scheduled = schedule_next_medication(context, chat_id, medication, taken_at, user_id)
        if scheduled:
            next_med, reminder_time, next_job_name = scheduled
            next_lines.append(
                f"Em sẽ nhắc Chủ nhân uống {next_med} lúc {reminder_time.strftime('%H:%M')} ạ."
            )
        else:
            next_lines.append("Chủ nhân đã hoàn thành lịch uống thuốc hôm nay ạ! 🎉")

    entry = log_medication(
        user_id, medication, taken_at=taken_at,
        next_job_name=next_job_name, eat_job_name=eat_job_name,
    )

    logged_date = datetime.fromisoformat(entry['timestamp']).strftime('%d/%m/%Y')
    lines = [
        f"Thưa Chủ nhân, em đã lưu lịch sử ạ:",
        "",
        f"  💊 Uống {medication} lúc {entry['time']} ngày {logged_date}",
        "",
    ]
    lines.extend(next_lines)
    lines.append("")
    lines.append("(Chủ nhân có thể xoá lịch sử này trong 2 phút)")
    text = "\n".join(lines)

    keyboard = InlineKeyboardMarkup([[
        InlineKeyboardButton("Xoá", callback_data=f"meddel_{entry['id']}")
    ]])
    await query.edit_message_text(text, reply_markup=keyboard)

    context.job_queue.run_once(
        remove_delete_button,
        when=MED_DELETE_WINDOW_SECONDS,
        data={"chat_id": chat_id, "message_id": query.message.message_id},
        name=f"medxoa_{entry['id']}",
    )


async def _medication_skip(query, context: ContextTypes.DEFAULT_TYPE) -> None:
    token = query.data.replace("medskip_", "")
    pending = pending_med_confirmations.pop(token, None)
    medication = pending["medication"] if pending else "thuốc"
    await query.edit_message_text(
        f"Thưa Chủ nhân, em đã huỷ ghi nhận uống {medication} ạ. Không có gì được lưu lại."
    )


async def _medication_delete(query, context: ContextTypes.DEFAULT_TYPE) -> None:
    entry_id = query.data.replace("meddel_", "")
    entry = find_medication_entry(query.from_user.id, entry_id)
    if not entry:
        await query.edit_message_text("Thưa Chủ nhân, lịch sử này không còn ạ.")
        return

    try:
        logged_at = datetime.fromisoformat(entry["timestamp"])
    except Exception:
        logged_at = None

    now = datetime.now(VN_TZ)
    if logged_at is None or (now - logged_at).total_seconds() > MED_DELETE_WINDOW_SECONDS:
        await query.edit_message_reply_markup(reply_markup=None)
        return

    next_job_name = entry.get("next_job_name")
    if next_job_name:
        for job in context.job_queue.get_jobs_by_name(next_job_name):
            job.schedule_removal()

    eat_job_name = entry.get("eat_job_name")
    if eat_job_name:
        for job in context.job_queue.get_jobs_by_name(eat_job_name):
            job.schedule_removal()

    delete_medication_entry(query.from_user.id, entry_id)

    cancelled_note = ""
    if next_job_name:
        chain = MEDICATION_CHAIN.get(entry["medication"])
        next_med = chain[0] if chain else None
        if next_med:
            cancelled_note = f"\nEm cũng đã huỷ nhắc nhở uống {next_med} ạ."
    if eat_job_name:
        cancelled_note += "\nEm cũng đã huỷ nhắc nhở đi ăn ạ."

    await query.edit_message_text(
        f"Thưa Chủ nhân, em đã xoá lịch sử uống {entry['medication']} lúc {entry['time']} ạ.{cancelled_note}"
    )


async def _medication_reminder_click(query, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle 'Đã uống sắt / vitamin' buttons from reminder messages."""
    key = query.data.replace("med_", "")
    medication = MED_CALLBACK_MAP.get(key)
    if not medication:
        return
    await show_medication_confirmation(query, context, medication, is_query=True)


async def handle_medication_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Dispatcher for all medication-related callbacks."""
    query = update.callback_query
    await query.answer()

    if not is_allowed(query.from_user.id):
        await query.edit_message_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ.")
        return

    data = query.data
    if data.startswith("medsave_"):
        await _medication_save(query, context)
    elif data.startswith("medskip_"):
        await _medication_skip(query, context)
    elif data.startswith("meddel_"):
        await _medication_delete(query, context)
    elif data.startswith("med_"):
        await _medication_reminder_click(query, context)


async def thuoc_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Show medication history grouped by date."""
    if not is_allowed(update.effective_user.id):
        await update.message.reply_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ.")
        return

    history = load_medication_history()
    items = history.get(str(update.effective_user.id), [])
    if not items:
        await update.message.reply_text(
            "Thưa Chủ nhân, chưa có lịch sử uống thuốc nào ạ.\n\n"
            "Chủ nhân xinh đẹp bắt đầu bằng cách nhắn: đã uống Gaviscon"
        )
        return

    by_date: dict = {}
    for item in items:
        by_date.setdefault(item["date"], []).append(item)

    msg = "Thưa Chủ nhân, đây là lịch sử uống thuốc của Chủ nhân ạ:\n\n"
    for d in sorted(by_date.keys(), reverse=True):
        dt = datetime.strptime(d, "%Y-%m-%d")
        msg += f"📅 {dt.strftime('%d/%m/%Y')}:\n"
        for entry in by_date[d]:
            msg += f"  • {entry['medication']}: {entry['time']}\n"
        msg += "\n"

    await update.message.reply_text(msg)


async def handle_ai_chat(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str) -> None:
    """Send user message to Gemini for a conversational AI response."""
    try:
        system_prompt = (
            "Bạn là Quản gia Ngaos - trợ lý thông minh trong một bot Telegram quản lý thu chi cá nhân. "
            "Bạn xưng 'em', gọi người dùng là 'Chủ nhân'. "
            "Luôn bắt đầu câu bằng 'Thưa Chủ nhân' và kết thúc bằng 'ạ'. "
            "Bạn có thể trả lời các câu hỏi chung, cho lời khuyên tài chính, "
            "hỗ trợ chủ nhân vui vẻ. Trả lời ngắn gọn, thân thiện, bằng tiếng Việt có dấu."
        )
        response = await asyncio.to_thread(
            gemini_model.generate_content,
            [system_prompt, text],
            generation_config={"max_output_tokens": 1024, "temperature": 0.7},
        )
        reply = response.text.strip()
        await update.message.reply_text(reply)
    except Exception as e:
        logger.error(f"AI chat error: {e}")
        await update.message.reply_text(
            "Thưa Chủ nhân, em gặp lỗi khi xử lý tin nhắn ạ. "
            "Chủ nhân xinh đẹp vui lòng thử lại sau ạ."
        )


async def extract_from_screenshot(image_bytes: bytes) -> Optional[dict]:
    """Use Gemini Vision to extract transfer info from a bank screenshot."""
    try:
        prompt = (
            "Đây là screenshot chuyển khoản ngân hàng. "
            "Hãy trích xuất thông tin và trả về JSON duy nhất (không có text khác) với format:\n"
            '{"amount": <số tiền integer>, "description": "<nội dung chuyển khoản>", "date": "<dd/mm/yy>"}\n'
            "Nếu không tìm thấy field nào thì để null. "
            "Số tiền là số nguyên không có dấu chấm/phẩy. "
            "QUAN TRỌNG: Nếu nội dung chuyển khoản không có dấu tiếng Việt (vd: 'an pizza', 'goi dau'), "
            "hãy tự động bổ sung dấu tiếng Việt cho đúng (vd: 'ăn pizza', 'gội đầu'). "
            "Chỉ trả về JSON, không giải thích gì thêm."
        )
        image_part = {"mime_type": "image/jpeg", "data": image_bytes}

        response = await asyncio.to_thread(
            gemini_model.generate_content,
            [prompt, image_part],
            generation_config={"max_output_tokens": 1024, "temperature": 0.0},
        )

        response_text = response.text.strip()
        logger.info(f"Gemini Vision response: {response_text}")

        # Parse JSON from response
        json_match = re.search(r'\{[^}]+\}', response_text)
        if json_match:
            data = json.loads(json_match.group())
            return {
                "amount": data.get("amount"),
                "description": data.get("description"),
                "date": data.get("date"),
            }
        return None
    except Exception as e:
        logger.error(f"Gemini Vision OCR error: {e}")
        return None


def parse_bank_transfer_text(text: str) -> Optional[dict]:
    """Parse bank transfer info from OCR text."""
    lines = [l.strip() for l in text.strip().split("\n") if l.strip()]

    # Extract amount - look for number near đ/VND or after "Thành công"
    amount = None
    for i, line in enumerate(lines):
        # Match lines with currency symbol
        m = re.search(r'(\d[\d\s.,]+)\s*(?:đ|VND|vnđ|vnd)', line, re.IGNORECASE)
        if m:
            num_str = re.sub(r'[^\d]', '', m.group(1))
            if num_str and int(num_str) >= 1000:
                amount = int(num_str)
                break
        # Match standalone large numbers right after "Thành công"
        if re.search(r'th[aà]nh c[oô]ng', line, re.IGNORECASE):
            for j in range(i + 1, min(i + 3, len(lines))):
                num_str = re.sub(r'[^\d]', '', lines[j])
                if num_str and len(num_str) >= 4:
                    amount = int(num_str)
                    break
            if amount:
                break

    # Also try: number followed by đ on same or next line
    if not amount:
        for i, line in enumerate(lines):
            # Number + đ on same line
            m = re.match(r'^(\d[\d\s]+)\s*đ?$', line.strip())
            if m:
                num_str = re.sub(r'[^\d]', '', m.group(1))
                if num_str and len(num_str) >= 4:
                    amount = int(num_str)
                    break
            # Number on this line, đ on next
            num_str = re.sub(r'[^\d]', '', line)
            if num_str and len(num_str) >= 4 and i + 1 < len(lines) and lines[i + 1].strip() in ('đ', 'd', 'VND'):
                amount = int(num_str)
                break

    if not amount:
        return None

    # Extract date
    trans_date = None
    for line in lines:
        date_match = re.search(r'(\d{1,2})[/-](\d{1,2})[/-](\d{2,4})', line)
        if date_match:
            d, m, y = date_match.group(1), date_match.group(2), date_match.group(3)
            if len(y) == 4:
                y = y[2:]
            trans_date = f"{d.zfill(2)}/{m.zfill(2)}/{y}"
            break

    # Extract description - collect all text between "Nội dung" and "Phí" labels
    # Also check one line before "Nội dung" label in case OCR puts content before label
    description = None
    label_keywords = ["phí", "phi", "mã giao", "ma giao", "mã tra", "ma tra",
                       "thời gian", "thoi gian", "thông tin", "thong tin"]
    desc_keywords = ["nội dung", "noi dung", "lời nhắn", "loi nhan"]

    for i, line in enumerate(lines):
        line_lower = line.lower()
        for kw in desc_keywords:
            if kw in line_lower:
                desc_parts = []
                # Check if label has text on same line
                after = re.sub(r'(?i)' + re.escape(kw) + r'[:\s]*', '', line).strip()
                if after:
                    desc_parts.append(after)
                # Also check one line BEFORE the label (OCR sometimes puts content before label)
                if i > 0:
                    prev_lower = lines[i - 1].lower()
                    if not any(lbl in prev_lower for lbl in label_keywords + desc_keywords + ["thành công", "thanh cong", "người nhận", "nguoi nhan"]):
                        # Check it's not a date or account number
                        if not re.match(r'^\d{1,2}[/-]\d{1,2}[/-]\d{2,4}$', lines[i - 1].strip()):
                            if not re.match(r'^\d{8,}$', lines[i - 1].strip()):
                                desc_parts.insert(0, lines[i - 1].strip())
                # Collect lines AFTER the label
                for j in range(i + 1, len(lines)):
                    next_lower = lines[j].lower()
                    if any(lbl in next_lower for lbl in label_keywords):
                        break
                    desc_parts.append(lines[j])
                if desc_parts:
                    description = " ".join(desc_parts).strip()
                break
        if description:
            break

    # Screenshot is always expense
    return {
        "amount": amount,
        "description": description,
        "date": trans_date,
        "is_income": False,
    }


def safe_int(value: str) -> int:
    """Parse an int from a string that may contain commas/dots as thousand separators."""
    return int(re.sub(r"[^\d]", "", str(value))) if value else 0


def is_allowed(user_id: int) -> bool:
    """Check if user is allowed to use the bot."""
    if not ALLOWED_USERS:
        return True
    return user_id in ALLOWED_USERS


# --- Telegram Handlers ---

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    await update.message.reply_text(
        f"Thưa Chủ nhân, em chào Chủ nhân ạ! Em là Quản gia Ngaos.\n"
        f"User ID của Chủ nhân: {user_id}\n\n"
        f"Chủ nhân có thể sử dụng như sau ạ:\n"
        f"  chi 150k bún đậu\n"
        f"  chi an 140k bún đậu 04/03\n"
        f"  chi mua 408k quần áo\n"
        f"  thu 15tr lương\n"
        f"  thu luong 15tr tháng 3\n\n"
        f"Các loại chi ạ:\n"
        f"  an = Ăn uống\n"
        f"  mua = Mua sắm\n"
        f"  hh = Đưa HH\n"
        f"  the = TT sao kê thẻ\n"
        f"  khac = Khác\n\n"
        f"Các loại thu ạ:\n"
        f"  luong = Lương\n"
        f"  thuong = Thưởng\n"
        f"  khac = Khác\n\n"
        f"Nhắc nhở ạ:\n"
        f"  nhắc tôi 3h chiều họp team\n"
        f"  nhắc 5 phút nữa uống nước\n"
        f"  /nhacnho - Xem danh sách nhắc nhở\n"
        f"  /xoanhac <id> - Huỷ nhắc nhở\n\n"
        f"Nhắc uống thuốc ạ:\n"
        f"  Nhắn: đã uống Gaviscon - Bắt đầu chuỗi nhắc\n"
        f"  Sau 2h em sẽ nhắc uống canxi (kèm nút)\n"
        f"  Sau 2h nữa em sẽ nhắc uống sắt (kèm nút)\n"
        f"  Sau 30 phút em sẽ nhắc đi ăn\n"
        f"  Sau 30 phút nữa em sẽ nhắc uống vitamin (kèm nút)\n"
        f"  Sau 2h nữa em sẽ nhắc uống canxi lần 2 (hoàn thành ngày)\n"
        f"  Nếu lỡ huỷ confirm, Chủ nhân nhắn lại 'đã uống canxi/sắt/vitamin' để lưu ạ.\n"
        f"  Nhắc thủ công: nhắc uống sắt 30 phút nữa\n"
        f"                 nhắc uống vitamin 1 tiếng nữa\n"
        f"  /thuoc - Xem lịch sử uống thuốc\n\n"
        f"Trợ lý AI ạ:\n"
        f"  Chủ nhân xinh đẹp cứ nhắn bất kỳ câu hỏi nào, em sẽ trả lời ạ!\n\n"
        f"Các lệnh khác ạ:\n"
        f"  /tonghop - Xem tổng hợp tháng này\n"
        f"  /xoa - Xem và xoá giao dịch gần đây\n"
        f"  Gửi hình screenshot CK - Em sẽ tự động đọc và nhập\n"
        f"  /help - Hướng dẫn sử dụng"
    )


async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "Thưa Chủ nhân, em xin hướng dẫn cách nhập thu chi ạ:\n\n"
        "1. Chi tiêu:\n"
        "   chi [số tiền] [nội dung]\n"
        "   chi [loại] [số tiền] [nội dung] [ngày]\n\n"
        "   VD:\n"
        "   chi 150k bún đậu\n"
        "   chi an 140k bún đậu 04/03\n"
        "   chi mua 1.5tr quần áo\n"
        "   chi 2tr đưa hh\n\n"
        "2. Thu nhập:\n"
        "   thu [số tiền] [nội dung]\n"
        "   thu luong 15tr\n\n"
        "3. Số tiền:\n"
        "   150k = 150,000\n"
        "   1.5tr = 1,500,000\n"
        "   2000000 = 2,000,000\n\n"
        "4. Ngày:\n"
        "   04/03 hoặc 04/03/26\n"
        "   Không ghi = hôm nay\n\n"
        "5. Xoá giao dịch:\n"
        "   /xoa - Xem 10 giao dịch gần đây và chọn xoá\n\n"
        "6. Screenshot chuyển khoản:\n"
        "   Chủ nhân xinh đẹp gửi hình screenshot CK ngân hàng\n"
        "   Em sẽ tự động đọc và nhập vào sheet ạ\n\n"
        "7. Nhắc nhở:\n"
        "   nhắc tôi 3h chiều họp team\n"
        "   nhắc 5 phút nữa uống nước\n"
        "   nhắc 8h sáng mai đi khám bệnh\n"
        "   /nhacnho - Xem danh sách nhắc nhở\n"
        "   /xoanhac <id> - Huỷ nhắc nhở\n\n"
        "8. Trợ lý AI:\n"
        "   Chủ nhân xinh đẹp cứ nhắn bất kỳ câu hỏi nào\n"
        "   Em sẽ trả lời bằng trí tuệ nhân tạo ạ"
    )


async def summary(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show monthly summary."""
    if not is_allowed(update.effective_user.id):
        await update.message.reply_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ. Chủ nhân chưa được cấp quyền sử dụng bot ạ.")
        return

    try:
        all_values = await asyncio.to_thread(lambda: get_sheet().get_all_values())
        current_month = datetime.now(VN_TZ).month

        total_thu = 0
        total_chi = 0
        categories = {}

        for row in all_values[1:]:
            if len(row) < 6:
                continue
            try:
                month_val = int(row[0]) if row[0] else 0
            except (ValueError, IndexError):
                continue

            if month_val != current_month:
                continue

            cat = row[1] if len(row) > 1 else ""
            thu = int(re.sub(r"[^\d]", "", row[3])) if row[3] else 0
            chi = int(re.sub(r"[^\d]", "", row[4])) if row[4] else 0

            total_thu += thu
            total_chi += chi

            if cat:
                categories[cat] = categories.get(cat, 0) + thu + chi

        msg = f"Thưa Chủ nhân, tổng hợp THÁNG {current_month} ạ:\n\n"
        msg += f"  Tổng THU: {total_thu:,.0f} VND\n".replace(",", ".")
        msg += f"  Tổng CHI: {total_chi:,.0f} VND\n".replace(",", ".")
        msg += f"  Còn lại:  {total_thu - total_chi:,.0f} VND\n\n".replace(",", ".")

        if categories:
            msg += "Chi tiết theo loại:\n"
            for cat, amount in sorted(categories.items()):
                msg += f"  {cat}: {amount:,.0f}\n".replace(",", ".")

        await update.message.reply_text(msg)
    except Exception as e:
        logger.error(f"Error getting summary: {e}")
        await update.message.reply_text(f"Thưa Chủ nhân, em gặp lỗi khi lấy tổng hợp ạ: {e}")


async def xoa_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show recent transactions with delete buttons."""
    if not is_allowed(update.effective_user.id):
        await update.message.reply_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ. Chủ nhân chưa được cấp quyền sử dụng bot ạ.")
        return

    try:
        all_values = await asyncio.to_thread(lambda: get_sheet().get_all_values())
        current_month = datetime.now(VN_TZ).month

        # Collect data rows for current month (with row numbers)
        data_rows = []
        for i, row in enumerate(all_values):
            if len(row) < 6:
                continue
            try:
                month_val = int(row[0]) if row[0] else 0
            except (ValueError, IndexError):
                continue
            if month_val == current_month:
                cat = row[1] if len(row) > 1 else ""
                desc = row[2] if len(row) > 2 else ""
                thu = row[3] if len(row) > 3 else ""
                chi = row[4] if len(row) > 4 else ""
                date_val = row[5] if len(row) > 5 else ""
                amount = chi if chi else thu
                type_str = "Chi" if chi else "Thu"
                data_rows.append({
                    "row_num": i + 1,  # 1-indexed
                    "type": type_str,
                    "cat": cat,
                    "desc": desc,
                    "amount": amount,
                    "date": date_val,
                })

        if not data_rows:
            await update.message.reply_text("Thưa Chủ nhân, tháng này chưa có giao dịch nào ạ.")
            return

        # Show last 10 transactions
        recent = data_rows[-10:]
        msg = f"Thưa Chủ nhân, đây là 10 giao dịch gần đây (Tháng {current_month}) ạ:\n\n"
        buttons = []
        for item in recent:
            amount_str = item["amount"]
            try:
                amount_str = f"{safe_int(amount_str):,.0f}".replace(",", ".")
            except (ValueError, TypeError):
                pass
            msg += f"  Dòng {item['row_num']}: {item['type']} {amount_str} - {item['desc']} ({item['date']})\n"
            buttons.append([
                InlineKeyboardButton(
                    f"Xoá dòng {item['row_num']}: {item['desc'][:20]}",
                    callback_data=f"del_{item['row_num']}"
                )
            ])

        keyboard = InlineKeyboardMarkup(buttons)
        await update.message.reply_text(msg, reply_markup=keyboard)

    except Exception as e:
        logger.error(f"Error in xoa_command: {e}")
        await update.message.reply_text(f"Thưa Chủ nhân, em gặp lỗi ạ: {e}")


async def handle_delete_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle delete button press."""
    query = update.callback_query
    await query.answer()

    if not is_allowed(query.from_user.id):
        await query.edit_message_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ.")
        return

    data = query.data
    if data.startswith("del_"):
        row_num = int(data.split("_")[1])

        # Show confirmation
        row_data = await asyncio.to_thread(lambda: get_row_data(get_sheet(), row_num))
        if not row_data:
            await query.edit_message_text("Thưa Chủ nhân, em không tìm thấy dòng này ạ. Có thể đã bị xoá rồi ạ.")
            return

        amount = row_data["chi"] if row_data["chi"] else row_data["thu"]
        amount_str = amount
        try:
            amount_str = f"{safe_int(amount):,.0f}".replace(",", ".")
        except (ValueError, TypeError):
            pass

        type_str = "Chi" if row_data["chi"] else "Thu"
        msg = (
            f"Thưa Chủ nhân, Chủ nhân có muốn xoá mục này không ạ?\n\n"
            f"  {type_str}: {amount_str} VND\n"
            f"  Loại: {row_data['category']}\n"
            f"  Nội dung: {row_data['description']}\n"
            f"  Ngày: {row_data['date']}\n"
            f"  Dòng: {row_num}"
        )

        keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("Xoá", callback_data=f"confirm_del_{row_num}"),
                InlineKeyboardButton("Huỷ", callback_data="cancel_del"),
            ]
        ])
        await query.edit_message_text(msg, reply_markup=keyboard)

    elif data.startswith("confirm_del_"):
        row_num = int(data.split("_")[2])
        try:
            result = await asyncio.to_thread(delete_from_sheet, row_num)
            await query.edit_message_text(result)
        except Exception as e:
            logger.error(f"Error deleting row: {e}")
            await query.edit_message_text(f"Thưa Chủ nhân, em gặp lỗi khi xoá ạ: {e}")

    elif data == "cancel_del":
        await query.edit_message_text("Thưa Chủ nhân, em đã huỷ xoá ạ.")


async def handle_ocr_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle OCR confirmation/edit callbacks."""
    query = update.callback_query
    await query.answer()

    if not is_allowed(query.from_user.id):
        await query.edit_message_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ.")
        return

    data = query.data
    if data.startswith("ocr_confirm_"):
        # Get stored OCR data from context
        ocr_key = data.replace("ocr_confirm_", "")
        ocr_data = context.user_data.get(f"ocr_{ocr_key}")
        if not ocr_data:
            await query.edit_message_text("Thưa Chủ nhân, dữ liệu đã hết hạn ạ. Chủ nhân vui lòng gửi lại hình giúp em ạ.")
            return

        try:
            msg, row_num = await asyncio.to_thread(add_to_sheet, ocr_data)
            keyboard = InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("Sửa", callback_data=f"edit_{row_num}"),
                    InlineKeyboardButton("Xoá", callback_data=f"del_{row_num}"),
                ]
            ])
            await query.edit_message_text(msg, reply_markup=keyboard)
        except Exception as e:
            logger.error(f"Error adding OCR data to sheet: {e}")
            await query.edit_message_text(f"Thưa Chủ nhân, em gặp lỗi khi ghi vào sheet ạ: {e}")

        # Clean up
        context.user_data.pop(f"ocr_{ocr_key}", None)

    elif data.startswith("ocr_cancel_"):
        ocr_key = data.replace("ocr_cancel_", "")
        context.user_data.pop(f"ocr_{ocr_key}", None)
        await query.edit_message_text("Thưa Chủ nhân, em đã huỷ ạ. Chủ nhân có thể gửi lại hình hoặc nhập thủ công ạ.")


async def handle_edit_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle edit category callbacks."""
    query = update.callback_query
    await query.answer()

    if not is_allowed(query.from_user.id):
        await query.edit_message_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ.")
        return

    data = query.data
    if data.startswith("editcat_"):
        # Format: editcat_{row_num}_{category_index}
        parts = data.split("_", 2)
        row_num = int(parts[1])
        cat_idx = int(parts[2])

        # Determine if THU or CHI from current row
        row_data = await asyncio.to_thread(lambda: get_row_data(get_sheet(), row_num))
        if not row_data:
            await query.edit_message_text("Thưa Chủ nhân, em không tìm thấy dòng này ạ.")
            return

        is_thu = row_data["category"].startswith("THU")
        cat_list = ALL_THU_TYPES if is_thu else ALL_CHI_TYPES
        if cat_idx < 0 or cat_idx >= len(cat_list):
            await query.edit_message_text("Thưa Chủ nhân, loại này không hợp lệ ạ.")
            return

        new_category = cat_list[cat_idx]
        msg = await asyncio.to_thread(update_category_in_sheet, row_num, new_category)
        keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("Sửa", callback_data=f"edit_{row_num}"),
                InlineKeyboardButton("Xoá", callback_data=f"del_{row_num}"),
            ]
        ])
        await query.edit_message_text(msg, reply_markup=keyboard)

    elif data.startswith("edit_"):
        row_num = int(data.replace("edit_", ""))

        # Read current row to determine THU/CHI
        row_data = await asyncio.to_thread(lambda: get_row_data(get_sheet(), row_num))
        if not row_data:
            await query.edit_message_text("Thưa Chủ nhân, em không tìm thấy dòng này ạ.")
            return

        is_thu = row_data["category"].startswith("THU")
        cat_list = ALL_THU_TYPES if is_thu else ALL_CHI_TYPES

        buttons = []
        for i, cat in enumerate(cat_list):
            buttons.append([InlineKeyboardButton(cat, callback_data=f"editcat_{row_num}_{i}")])

        keyboard = InlineKeyboardMarkup(buttons)
        await query.edit_message_text(
            f"Thưa Chủ nhân, xin Chủ nhân chọn loại mới cho: {row_data['description']}\n"
            f"Loại hiện tại: {row_data['category']}",
            reply_markup=keyboard,
        )


async def nhacnho_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all active reminders."""
    if not is_allowed(update.effective_user.id):
        await update.message.reply_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ.")
        return

    chat_id = update.effective_chat.id
    items = reminders_store.get(chat_id, [])
    # Filter out past reminders
    now = datetime.now(VN_TZ)
    items = [r for r in items if r["time"] > now]
    reminders_store[chat_id] = items

    if not items:
        await update.message.reply_text(
            "Thưa Chủ nhân, hiện tại không có nhắc nhở nào ạ.\n\n"
            "Chủ nhân xinh đẹp có thể đặt nhắc nhở bằng cách nhắn:\n"
            "  nhắc tôi 3h chiều họp team\n"
            "  nhắc 5 phút nữa uống nước"
        )
        return

    msg = "Thưa Chủ nhân, đây là danh sách nhắc nhở ạ:\n\n"
    for r in items:
        msg += f"  #{r['id']} - {r['time'].strftime('%H:%M ngày %d/%m')} - {r['content']}\n"
    msg += "\nĐể huỷ, Chủ nhân dùng: /xoanhac <id>"
    await update.message.reply_text(msg)


async def xoanhac_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Cancel a reminder by ID."""
    if not is_allowed(update.effective_user.id):
        await update.message.reply_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ.")
        return

    args = context.args
    if not args:
        await update.message.reply_text(
            "Thưa Chủ nhân, Chủ nhân vui lòng nhập ID nhắc nhở cần huỷ ạ.\n"
            "Ví dụ: /xoanhac 1"
        )
        return

    try:
        reminder_id = int(args[0])
    except ValueError:
        await update.message.reply_text("Thưa Chủ nhân, ID không hợp lệ ạ.")
        return

    chat_id = update.effective_chat.id
    items = reminders_store.get(chat_id, [])
    target = None
    for r in items:
        if r["id"] == reminder_id:
            target = r
            break

    if not target:
        await update.message.reply_text(f"Thưa Chủ nhân, em không tìm thấy nhắc nhở #{reminder_id} ạ.")
        return

    # Remove job from queue
    jobs = context.job_queue.get_jobs_by_name(target["job_name"])
    for job in jobs:
        job.schedule_removal()

    # Remove from store
    reminders_store[chat_id] = [r for r in items if r["id"] != reminder_id]

    await update.message.reply_text(
        f"Thưa Chủ nhân, em đã huỷ nhắc nhở #{reminder_id} ạ: {target['content']}"
    )


async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle incoming messages - parse and add to sheet."""
    if not is_allowed(update.effective_user.id):
        await update.message.reply_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ. Chủ nhân chưa được cấp quyền sử dụng bot ạ.")
        return

    text = update.message.text
    if not text:
        return

    lower = text.lower().strip()
    normalized = unicodedata.normalize("NFC", lower)

    # 1) Medication taken - "đã uống <med>" opens the same Lưu/Huỷ confirmation as the button.
    med_taken = parse_medication_taken_text(text)
    if med_taken:
        taken_at = None
        if med_taken["time"]:
            h, m = med_taken["time"]
            now = datetime.now(VN_TZ)
            taken_at = now.replace(hour=h, minute=m, second=0, microsecond=0)
            # If parsed time is in the future (e.g. user wrote 23:00 but it's now 01:00), assume yesterday.
            if taken_at > now:
                taken_at -= timedelta(days=1)
        logger.info(
            f"Medication trigger: {med_taken['medication']} taken_at={taken_at} "
            f"from user {update.effective_user.id}"
        )
        await show_medication_confirmation(
            update.message, context, med_taken["medication"], is_query=False, taken_at=taken_at
        )
        return

    # 2) Manual medication reminder - "nhắc uống sắt/vitamin X phút/tiếng nữa"
    med_reminder = parse_med_reminder_request(text)
    if med_reminder:
        await handle_med_reminder_schedule(update, context, med_reminder)
        return

    # 3) Generic reminder request
    reminder_keywords = ("nhắc", "nhac", "nhớ", "nho ", "hẹn", "hen ",
                         "phút nữa", "phut nua", "tiếng nữa", "tieng nua",
                         "remind", "alarm", "báo thức", "bao thuc")
    if any(kw in lower for kw in reminder_keywords):
        await handle_reminder_request(update, context, text)
        return

    # 4) Thu/chi transaction
    data = await asyncio.to_thread(parse_message, text)
    if data is None:
        if lower.startswith("thu") or lower.startswith("chi"):
            await update.message.reply_text(
                "Thưa Chủ nhân, em không hiểu ạ. Chủ nhân xinh đẹp vui lòng nhập theo mẫu:\n"
                "  chi 150k bún đậu\n"
                "  thu 5tr lương"
            )
            return
        # 5) AI assistant fallback
        await handle_ai_chat(update, context, text)
        return

    try:
        msg, row_num = await asyncio.to_thread(add_to_sheet, data)
        keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("Sửa", callback_data=f"edit_{row_num}"),
                InlineKeyboardButton("Xoá", callback_data=f"del_{row_num}"),
            ]
        ])
        await update.message.reply_text(msg, reply_markup=keyboard)
    except Exception as e:
        logger.error(f"Error adding to sheet: {e}")
        await update.message.reply_text(f"Thưa Chủ nhân, em gặp lỗi khi ghi vào sheet ạ: {e}")


async def handle_photo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle photo messages - OCR bank transfer screenshots."""
    if not is_allowed(update.effective_user.id):
        await update.message.reply_text("Thưa Chủ nhân, em không nhận ra Chủ nhân ạ. Chủ nhân chưa được cấp quyền sử dụng bot ạ.")
        return

    await update.message.reply_text("Thưa Chủ nhân, em đang đọc hình ạ...")

    try:
        # Get the highest resolution photo
        photo = update.message.photo[-1]
        file = await context.bot.get_file(photo.file_id)

        # Download to memory
        bio = BytesIO()
        await file.download_to_memory(bio)
        image_bytes = bio.getvalue()

        # Extract info using Gemini Vision
        extracted = await extract_from_screenshot(image_bytes)

        if not extracted:
            await update.message.reply_text(
                "Thưa Chủ nhân, em không đọc được thông tin từ hình ạ.\n"
                "Chủ nhân vui lòng nhập thủ công:\n"
                "  chi 150k bún đậu"
            )
            return

        # Check what info we have
        amount = extracted.get("amount")
        raw_description = extracted.get("description", "")
        trans_date = extracted.get("date")

        if not amount:
            await update.message.reply_text(
                "Thưa Chủ nhân, em không đọc được số tiền từ hình ạ.\n"
                "Chủ nhân vui lòng nhập thủ công:\n"
                "  chi [số tiền] [nội dung]"
            )
            return

        # Default date to today if not found
        if not trans_date:
            trans_date = date.today().strftime("%d/%m/%y")

        # Screenshot is always expense - detect category from description
        description = "Chuyen khoan"
        if raw_description:
            # Extract short description from raw (remove sender name pattern)
            desc_clean = re.sub(r'^[A-Z\s]+(chuyen tien|chuyển tiền|ck)\s*', '', raw_description, flags=re.IGNORECASE).strip()
            description = desc_clean if desc_clean else raw_description

        # Use history lookup, then simple rules
        category = await asyncio.to_thread(guess_category_from_history, description, False)
        if category is None:
            desc_lower = description.lower()
            if any(w in desc_lower for w in ("ăn", "uống", "an ", "uong")):
                category = "CHI - Ăn uống"
            else:
                category = "CHI - Khác"

        month = datetime.strptime(trans_date, "%d/%m/%y").month

        ocr_data = {
            "is_income": False,
            "category": category,
            "description": description,
            "amount": amount,
            "date": trans_date,
            "month": month,
            "note": raw_description or "",
        }

        # Store OCR data with unique key
        ocr_key = str(update.message.message_id)
        context.user_data[f"ocr_{ocr_key}"] = ocr_data

        # Show extracted info and ask for confirmation
        amount_fmt = f"{amount:,.0f}".replace(",", ".")
        msg = (
            f"Thưa Chủ nhân, em đọc được từ hình ạ:\n\n"
            f"  Chi: {amount_fmt} VND\n"
            f"  Loại: {category}\n"
            f"  Nội dung: {description}\n"
            f"  Ngày: {trans_date}\n"
            f"  Ghi chú: {raw_description}\n\n"
            f"Chủ nhân có muốn em ghi vào sheet không ạ?"
        )

        keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("Xác nhận", callback_data=f"ocr_confirm_{ocr_key}"),
                InlineKeyboardButton("Huỷ", callback_data=f"ocr_cancel_{ocr_key}"),
            ]
        ])
        await update.message.reply_text(msg, reply_markup=keyboard)

    except Exception as e:
        logger.error(f"Error processing photo: {e}")
        await update.message.reply_text(f"Thưa Chủ nhân, em gặp lỗi khi xử lý hình ạ: {e}")


def main():
    # Kill any other bot.py processes before starting
    my_pid = os.getpid()
    killed = False
    result = subprocess.run(["pgrep", "-f", "python.*bot.py"], capture_output=True, text=True)
    for pid_str in result.stdout.strip().split("\n"):
        if pid_str.strip() and int(pid_str.strip()) != my_pid:
            try:
                os.kill(int(pid_str.strip()), 9)
                killed = True
            except OSError:
                pass
    if killed:
        time.sleep(3)  # Wait for Telegram to release the polling session

    if not TELEGRAM_BOT_TOKEN or TELEGRAM_BOT_TOKEN == "your_telegram_bot_token_here":
        print("ERROR: Chưa cấu hình TELEGRAM_BOT_TOKEN trong file .env")
        return

    app = Application.builder().token(TELEGRAM_BOT_TOKEN).concurrent_updates(True).build()

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(CommandHandler("tonghop", summary))
    app.add_handler(CommandHandler("xoa", xoa_command))
    app.add_handler(CommandHandler("nhacnho", nhacnho_command))
    app.add_handler(CommandHandler("xoanhac", xoanhac_command))
    app.add_handler(CommandHandler("thuoc", thuoc_command))

    # Photo handler for OCR
    app.add_handler(MessageHandler(filters.PHOTO, handle_photo))

    # Callback handlers for inline buttons
    app.add_handler(CallbackQueryHandler(handle_delete_callback, pattern=r"^(del_|confirm_del_|cancel_del)"))
    app.add_handler(CallbackQueryHandler(handle_edit_callback, pattern=r"^(edit_|editcat_)"))
    app.add_handler(CallbackQueryHandler(handle_ocr_callback, pattern=r"^ocr_"))
    app.add_handler(CallbackQueryHandler(handle_medication_callback, pattern=r"^med"))

    # Text message handler
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))

    print("Quản gia Ngaos đang chạy...")
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
