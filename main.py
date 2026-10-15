#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Minecraft News Bot
==================

Телеграм-бот, который:

* при добавлении в канал (ID: 4421879537) начинает парсить открытые
  официальные источники новостей Minecraft и автоматически постить
  свежие новости в этот канал;
* вместе с постом отправляет картинку из источника (если она есть у новости,
  если картинки нет — пост уходит без изображения);
* в личных сообщениях показывает кнопку «Проверка» (только для @mellfreezy),
  которая запрашивает одну свежую новость из подключённых источников
  и публикует её в канал.

Источники (только проверенные, открытые, без API-ключей):

1. Официальный контент-сервис лаунчера Minecraft от Mojang Studios:
   https://launchercontent.mojang.com/v2/javaNews.json
   https://launchercontent.mojang.com/v2/bedrockNews.json
2. Официальная RSS-лента сайта minecraft.net:
   https://www.minecraft.net/en-us/feeds/rss/articles

Единственный параметр окружения — токен бота в файле .env:

    BOT_TOKEN=1234567890:AA...
"""

from __future__ import annotations

import asyncio
import datetime as dt
import hashlib
import html
import json
import logging
import os
import re
import sys
import time
from dataclasses import dataclass
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Optional
from urllib.parse import urljoin

import feedparser
import httpx
from dotenv import load_dotenv
from telegram import (
    Bot,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    LinkPreviewOptions,
    Update,
)
from telegram.constants import ChatMemberStatus, ChatType, ParseMode
from telegram.error import BadRequest, Forbidden, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ---------------------------------------------------------------------------
# НАСТРОЙКИ — всё, кроме токена бота, лежит прямо в коде
# ---------------------------------------------------------------------------

BASE_DIR = Path(__file__).resolve().parent
STATE_FILE = BASE_DIR / "posted_news.json"   # сюда бот запоминает уже опубликованное
LOG_FILE = BASE_DIR / "bot.log"

# ID канала, в который бот публикует новости (указан владельцем: 4421879537).
# Telegram выдаёт каналам/супергруппам ID с префиксом -100, поэтому основной
# вариант — -1004421879537, второй — подстраховка для обычных групп.
CHANNEL_ID_RAW = 4421879537
CHANNEL_ID_MAIN = int(f"-100{CHANNEL_ID_RAW}")
CHANNEL_ID_FALLBACK = -CHANNEL_ID_RAW

# Юзернейм единственного пользователя, которому доступна кнопка «Проверка»
ADMIN_USERNAME = "mellfreezy"

CHECK_INTERVAL_MINUTES = 120   # период проверки источников (2 часа)
MAX_POSTS_PER_CYCLE = 3        # максимум новостей за один плановый проход
MAX_POSTS_ON_START = 3         # максимум новостей сразу после добавления в канал
PAUSE_BETWEEN_POSTS = 3        # пауза между постами, сек (антифлуд)
HTTP_TIMEOUT = 20              # таймаут загрузки источников, сек
MAX_SEEN_ENTRIES = 2000        # сколько опубликованных ID хранить в состоянии

USER_AGENT = "Mozilla/5.0 (compatible; MinecraftNewsBot/1.0)"

ACTIVE_STATUSES = (
    ChatMemberStatus.MEMBER,
    ChatMemberStatus.ADMINISTRATOR,
    ChatMemberStatus.OWNER,
)

logger = logging.getLogger("mc-news-bot")

# ---------------------------------------------------------------------------
# ИСТОЧНИКИ НОВОСТЕЙ (официальные / проверенные, открытые API без ключей)
# ---------------------------------------------------------------------------

MOJANG_API = "https://launchercontent.mojang.com"
MINECRAFT_NET_RSS = "https://www.minecraft.net/en-us/feeds/rss/articles"


@dataclass(frozen=True)
class Source:
    key: str      # внутренний ключ источника
    name: str     # человекочитаемое название для подписи поста
    kind: str     # "mojang" | "rss"
    url: str


SOURCES: tuple[Source, ...] = (
    Source(
        "launcher-java-news",
        "Лаунчер Minecraft — Java Edition (официальный источник Mojang)",
        "mojang",
        f"{MOJANG_API}/v2/javaNews.json",
    ),
    Source(
        "launcher-bedrock-news",
        "Лаунчер Minecraft — Bedrock Edition (официальный источник Mojang)",
        "mojang",
        f"{MOJANG_API}/v2/bedrockNews.json",
    ),
    Source(
        "minecraft-net",
        "Minecraft.net (официальный сайт)",
        "rss",
        MINECRAFT_NET_RSS,
    ),
)


@dataclass
class NewsItem:
    source_key: str
    source_name: str
    item_id: str
    title: str
    text: str
    url: str
    published: Optional[dt.datetime]
    image_url: Optional[str]

    @property
    def uid(self) -> str:
        return f"{self.source_key}:{self.item_id}"

    @property
    def title_hash(self) -> str:
        norm = re.sub(r"\s+", " ", self.title).strip().lower()
        return "title:" + hashlib.md5(norm.encode("utf-8")).hexdigest()


# ---------------------------------------------------------------------------
# ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ
# ---------------------------------------------------------------------------


def normalize_chat_id(chat_id: int) -> int:
    """Приводит ID чата к «сырому» виду (без префиксов -100 / -)."""
    s = str(chat_id)
    if s.startswith("-100"):
        return int(s[4:])
    return abs(chat_id)


def is_target_channel(chat_id: int) -> bool:
    return normalize_chat_id(chat_id) == CHANNEL_ID_RAW


def strip_html(raw: str) -> str:
    """Убирает HTML-теги и приводит текст к читаемому виду."""
    if not raw:
        return ""
    text = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", raw, flags=re.S | re.I)
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def extract_image_from_html(raw: str) -> Optional[str]:
    """Достаёт URL первой картинки из HTML-блока (например, из RSS-описания)."""
    if not raw:
        return None
    match = re.search(r'<img[^>]+src=["\']([^"\']+)["\']', raw, flags=re.I)
    if not match:
        return None
    url = match.group(1).strip()
    if url.startswith("http://"):
        url = "https://" + url[len("http://"):]
    return url if url.startswith("https://") else None


def parse_mojang_date(value: Any) -> Optional[dt.datetime]:
    if not value:
        return None
    s = str(value).strip()
    for fmt in ("%Y-%m-%d", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M:%S"):
        try:
            return dt.datetime.strptime(s[:19], fmt).replace(tzinfo=dt.timezone.utc)
        except ValueError:
            continue
    try:
        parsed = dt.datetime.fromisoformat(s)
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=dt.timezone.utc)
        return parsed.astimezone(dt.timezone.utc)
    except ValueError:
        return None


def parse_rss_date(struct_time: Any) -> Optional[dt.datetime]:
    if not struct_time:
        return None
    try:
        return dt.datetime.fromtimestamp(time.mktime(struct_time), tz=dt.timezone.utc)
    except (OverflowError, OSError, TypeError, ValueError):
        return None


def _image_title_line(item: NewsItem) -> str:  # pragma: no cover - зарезервировано
    return ""


# ---------------------------------------------------------------------------
# ЗАГРУЗКА И РАЗБОР ИСТОЧНИКОВ
# ---------------------------------------------------------------------------


async def _http_get(client: httpx.AsyncClient, url: str) -> Optional[bytes]:
    try:
        response = await client.get(url)
        response.raise_for_status()
        return response.content
    except Exception as exc:  # noqa: BLE001 — любой сетевой сбой не должен ронять бота
        logger.warning("Не удалось загрузить %s: %s", url, exc)
        return None


def parse_mojang(source: Source, raw: bytes) -> list[NewsItem]:
    try:
        data = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError):
        logger.warning("Источник %s вернул не JSON", source.url)
        return []

    entries = data.get("entries") if isinstance(data, dict) else data
    if not isinstance(entries, list):
        return []

    items: list[NewsItem] = []
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        title = str(entry.get("title") or "").strip()
        if not title:
            continue
        item_id = str(entry.get("id") or entry.get("version") or title)[:120]
        text = strip_html(str(entry.get("shortText") or entry.get("body") or ""))[:1200]

        image = entry.get("image")
        image_url = None
        if isinstance(image, dict) and image.get("url"):
            image_url = urljoin(MOJANG_API + "/", str(image["url"]).lstrip("/"))
            if image_url.startswith("http://"):
                image_url = "https://" + image_url[len("http://"):]

        url = str(entry.get("readMoreLink") or "").strip()

        items.append(
            NewsItem(
                source_key=source.key,
                source_name=source.name,
                item_id=item_id,
                title=title,
                text=text,
                url=url,
                published=parse_mojang_date(entry.get("date")),
                image_url=image_url,
            )
        )
    return items


def parse_rss(source: Source, raw: bytes) -> list[NewsItem]:
    parsed = feedparser.parse(raw)
    items: list[NewsItem] = []
    for entry in parsed.entries[:30]:
        title = str(entry.get("title") or "").strip()
        if not title:
            continue
        link = str(entry.get("link") or "").strip()
        item_id = str(entry.get("id") or link or title)[:200]
        summary = str(entry.get("summary") or entry.get("description") or "")

        image_url = None
        media = entry.get("media_content") or []
        for m in media:
            candidate = str(m.get("url") or "")
            if candidate and (m.get("medium") == "image" or candidate.lower().endswith(
                (".jpg", ".jpeg", ".png", ".webp")
            )):
                image_url = candidate
                break
        if not image_url:
            for l in entry.get("links") or []:
                if str(l.get("rel")) == "enclosure" and str(l.get("type", "")).startswith("image"):
                    image_url = str(l.get("href") or "")
                    break
        if not image_url:
            image_url = extract_image_from_html(summary)
        if image_url and image_url.startswith("http://"):
            image_url = "https://" + image_url[len("http://"):]

        items.append(
            NewsItem(
                source_key=source.key,
                source_name=source.name,
                item_id=item_id,
                title=title,
                text=strip_html(summary)[:1200],
                url=link,
                published=parse_rss_date(entry.get("published_parsed") or entry.get("updated_parsed")),
                image_url=image_url if image_url and image_url.startswith("https://") else None,
            )
        )
    return items


async def fetch_source(client: httpx.AsyncClient, source: Source) -> list[NewsItem]:
    raw = await _http_get(client, source.url)
    if not raw:
        return []
    if source.kind == "mojang":
        return parse_mojang(source, raw)
    return parse_rss(source, raw)


async def fetch_all_news() -> list[NewsItem]:
    """Собирает новости со всех источников, сортирует от новых к старым."""
    headers = {"User-Agent": USER_AGENT, "Accept": "*/*"}
    async with httpx.AsyncClient(
        headers=headers, timeout=HTTP_TIMEOUT, follow_redirects=True
    ) as client:
        results = await asyncio.gather(
            *(fetch_source(client, source) for source in SOURCES),
            return_exceptions=True,
        )

    items: list[NewsItem] = []
    for source, result in zip(SOURCES, results):
        if isinstance(result, BaseException):
            logger.warning("Источник %s недоступен: %s", source.name, result)
            continue
        logger.info("Источник «%s»: получено %d новостей", source.name, len(result))
        items.extend(result)

    # от новых к старым
    epoch = dt.datetime.min.replace(tzinfo=dt.timezone.utc)
    items.sort(key=lambda i: i.published or epoch, reverse=True)

    # убираем дубли по названию (одна и та же новость в разных лентах)
    unique: list[NewsItem] = []
    seen_titles: set[str] = set()
    for item in items:
        if item.title_hash in seen_titles:
            continue
        seen_titles.add(item.title_hash)
        unique.append(item)
    return unique


# ---------------------------------------------------------------------------
# СОСТОЯНИЕ (чтобы не постить одну и ту же новость дважды)
# ---------------------------------------------------------------------------


def load_seen() -> dict[str, None]:
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    keys = data.get("posted", []) if isinstance(data, dict) else []
    return dict.fromkeys(str(k) for k in keys)


def save_seen(seen: dict[str, None]) -> None:
    keys = list(seen.keys())[-MAX_SEEN_ENTRIES:]
    try:
        STATE_FILE.write_text(
            json.dumps({"posted": keys}, ensure_ascii=False), encoding="utf-8"
        )
    except OSError as exc:
        logger.warning("Не удалось сохранить состояние: %s", exc)


def is_seen(seen: dict[str, None], item: NewsItem) -> bool:
    return item.uid in seen or item.title_hash in seen


def remember(seen: dict[str, None], item: NewsItem) -> None:
    seen[item.uid] = None
    seen[item.title_hash] = None


# ---------------------------------------------------------------------------
# ФОРМАТИРОВАНИЕ И ПУБЛИКАЦИЯ ПОСТОВ
# ---------------------------------------------------------------------------


def build_caption(item: NewsItem) -> str:
    """Собирает подпись поста с HTML-форматированием, вписываясь в лимиты."""
    limit = 1024 if item.image_url else 4096

    title = html.escape(" ".join(item.title.split()))[:200]
    head = f"<b>{title}</b>"

    date_line = ""
    if item.published:
        date_line = "\n🗓 " + item.published.astimezone(dt.timezone.utc).strftime("%d.%m.%Y")
    link_line = ""
    if item.url:
        link_line = f'\n🔗 <a href="{html.escape(item.url, quote=True)}">Читать полностью</a>'
    footer = f"{link_line}\n📻 Источник: {html.escape(item.source_name)}{date_line}\n\n#minecraft #новости"

    body = item.text.strip()
    budget = limit - len(head) - len(footer) - 2  # 2 символа на "\n\n"
    if budget < 0:
        budget = 0
    if len(body) > budget:
        body = body[: max(0, budget - 1)].rstrip(" ,.;:-…") + "…"

    caption = f"{head}\n\n{body}{footer}" if body else f"{head}{footer}"
    return caption


async def post_item(bot: Bot, item: NewsItem, chat_id: Optional[int] = None) -> bool:
    """Публикует новость в канал. С картинкой, если она есть у новости."""
    target = chat_id or CHANNEL_ID_MAIN
    caption = build_caption(item)

    if item.image_url:
        try:
            await bot.send_photo(
                chat_id=target,
                photo=item.image_url,
                caption=caption,
                parse_mode=ParseMode.HTML,
            )
            return True
        except BadRequest as exc:
            logger.warning("Картинка не отправилась (%s), публикую текстом: %s", exc, item.image_url)
        except Forbidden:
            logger.error("Нет прав на публикацию в канал %s", target)
            return False

    try:
        await bot.send_message(
            chat_id=target,
            text=caption,
            parse_mode=ParseMode.HTML,
            link_preview_options=LinkPreviewOptions(is_disabled=True),
        )
        return True
    except BadRequest as exc:
        logger.warning("Пост с HTML не прошёл (%s), пробую без форматирования", exc)
        plain = f"{item.title}\n\n{item.text}\n\n{item.url}\n📻 {item.source_name}"
        try:
            await bot.send_message(
                chat_id=target,
                text=plain[:4096],
                link_preview_options=LinkPreviewOptions(is_disabled=True),
            )
            return True
        except TelegramError as exc2:
            logger.error("Не удалось опубликовать новость: %s", exc2)
    except Forbidden:
        logger.error("Бот удалён из канала %s или не имеет прав на публикацию", target)
    except TelegramError as exc:
        logger.error("Ошибка Telegram при публикации: %s", exc)
    return False


async def publish_new_items(
    bot: Bot, limit: int, chat_id: Optional[int] = None
) -> int:
    """Забирает новости из источников и публикует ещё не опубликованные."""
    items = await fetch_all_news()
    if not items:
        logger.warning("Ни один источник не вернул новости")
        return 0

    seen = load_seen()
    posted = 0
    for item in items:
        if posted >= limit:
            break
        if is_seen(seen, item):
            continue
        if await post_item(bot, item, chat_id):
            remember(seen, item)
            save_seen(seen)
            posted += 1
            logger.info("Опубликовано: %s", item.title)
            if posted < limit:
                await asyncio.sleep(PAUSE_BETWEEN_POSTS)
    return posted


# ---------------------------------------------------------------------------
# ФОНОВЫЙ ПЛАНИРОВЩИК
# ---------------------------------------------------------------------------


async def scheduler_loop(app: Application) -> None:
    while True:
        await asyncio.sleep(CHECK_INTERVAL_MINUTES * 60)
        if not app.bot_data.get("channel_active"):
            continue
        try:
            count = await publish_new_items(
                app.bot,
                MAX_POSTS_PER_CYCLE,
                app.bot_data.get("channel_chat_id"),
            )
            if count:
                logger.info("По расписанию опубликовано новостей: %d", count)
        except Exception:  # noqa: BLE001
            logger.exception("Сбой цикла публикации по расписанию")


async def post_init(app: Application) -> None:
    """Запускается после поднятия бота: проверяет канал и стартует планировщик."""
    app.bot_data.setdefault("channel_active", False)
    app.bot_data.setdefault("channel_chat_id", None)
    try:
        for candidate in (CHANNEL_ID_MAIN, CHANNEL_ID_FALLBACK):
            try:
                member = await app.bot.get_chat_member(candidate, app.bot.id)
            except TelegramError:
                continue
            if member.status in ACTIVE_STATUSES:
                app.bot_data["channel_active"] = True
                app.bot_data["channel_chat_id"] = candidate
                logger.info(
                    "Бот уже состоит в канале (%s) — включаю автопостинг.", candidate
                )
                app.create_task(publish_new_items(app.bot, MAX_POSTS_ON_START, candidate))
                break
        else:
            logger.info(
                "Бот пока не добавлен в канал с ID %d — жду добавления.", CHANNEL_ID_RAW
            )
    except Exception:  # noqa: BLE001
        logger.exception("Не удалось проверить канал при старте")
    app.create_task(scheduler_loop(app))


# ---------------------------------------------------------------------------
# ХЭНДЛЕРЫ TELEGRAM
# ---------------------------------------------------------------------------


def is_admin_user(user: Any) -> bool:
    return bool(
        user
        and getattr(user, "username", None)
        and user.username.lower().lstrip("@") == ADMIN_USERNAME.lstrip("@").lower()
    )


def admin_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [[InlineKeyboardButton("🔍 Проверка", callback_data="check")]]
    )


async def show_admin_panel(update: Update) -> None:
    message = update.effective_message
    if message is None:
        return
    if not is_admin_user(update.effective_user):
        await message.reply_text(
            f"⛔ Панель управления доступна только @{ADMIN_USERNAME}."
        )
        return
    await message.reply_text(
        "👋 Привет! Это панель управления Minecraft News Bot.\n\n"
        "Кнопка ниже запрашивает одну свежую новость по Minecraft из "
        "официальных источников и сразу публикует её в канал.\n\n"
        f"Автопостинг работает сам — бот публикует новости в канал "
        f"каждые {CHECK_INTERVAL_MINUTES // 60} ч после добавления в него.",
        reply_markup=admin_keyboard(),
    )


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_chat and update.effective_chat.type != ChatType.PRIVATE:
        return
    await show_admin_panel(update)


async def on_private_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await show_admin_panel(update)


async def on_check_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Кнопка «Проверка»: 1 свежая новость из источников -> в канал."""
    query = update.callback_query
    if query is None:
        return

    if not is_admin_user(query.from_user):
        await query.answer(
            f"⛔ Кнопка доступна только @{ADMIN_USERNAME}.", show_alert=True
        )
        return

    await query.answer("⏳ Запрашиваю новость…")
    status = await context.bot.send_message(
        query.from_user.id, "⏳ Запрашиваю одну свежую новость из источников…"
    )

    try:
        items = await fetch_all_news()
    except Exception as exc:  # noqa: BLE001
        logger.exception("Ошибка получения новостей по кнопке: %s", exc)
        items = []

    if not items:
        await status.edit_text(
            "⚠️ Не удалось получить новости из источников. Попробуй позже."
        )
        return

    seen = load_seen()
    item = next((i for i in items if not is_seen(seen, i)), items[0])

    chat_id = context.bot_data.get("channel_chat_id")
    if await post_item(context.bot, item, chat_id):
        remember(seen, item)
        save_seen(seen)
        await status.edit_text(
            f"✅ Новость отправлена в канал:\n\n📰 {html.escape(item.title)}"
        )
    else:
        await status.edit_text(
            "⚠️ Не удалось опубликовать новость. Убедись, что бот добавлен в канал "
            "и у него есть право публиковать сообщения."
        )


async def on_my_chat_member(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Срабатывает при добавлении/удалении бота в канале."""
    change = update.my_chat_member
    if change is None or change.chat is None:
        return
    if not is_target_channel(change.chat.id):
        return

    status = change.new_chat_member.status
    chat_id = change.chat.id

    if status in ACTIVE_STATUSES:
        context.bot_data["channel_active"] = True
        context.bot_data["channel_chat_id"] = chat_id
        logger.info("Бот добавлен в канал %s — включаю автопостинг.", chat_id)
        try:
            await context.bot.send_message(
                chat_id,
                "🟢 <b>Minecraft News Bot</b> подключён!\n\n"
                f"Буду постить свежие новости о Minecraft каждые "
                f"{CHECK_INTERVAL_MINUTES // 60} ч. "
                f"Сейчас подтяну последние новости…",
                parse_mode=ParseMode.HTML,
                link_preview_options=LinkPreviewOptions(is_disabled=True),
            )
        except TelegramError as exc:
            logger.warning("Не удалось отправить приветствие в канал: %s", exc)
        context.application.create_task(
            publish_new_items(context.bot, MAX_POSTS_ON_START, chat_id)
        )
    else:
        context.bot_data["channel_active"] = False
        logger.info("Бот удалён из канала %s — автопостинг остановлен.", chat_id)


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.exception("Необработанная ошибка", exc_info=context.error)


# ---------------------------------------------------------------------------
# ТОЧКА ВХОДА
# ---------------------------------------------------------------------------


def setup_logging() -> None:
    fmt = "%(asctime)s | %(levelname)-7s | %(name)s | %(message)s"
    root = logging.getLogger()
    root.setLevel(logging.INFO)
    root.handlers.clear()

    stream = logging.StreamHandler(sys.stdout)
    stream.setFormatter(logging.Formatter(fmt))
    root.addHandler(stream)

    file_handler = RotatingFileHandler(
        LOG_FILE, maxBytes=2_000_000, backupCount=2, encoding="utf-8"
    )
    file_handler.setFormatter(logging.Formatter(fmt))
    root.addHandler(file_handler)

    logging.getLogger("httpx").setLevel(logging.WARNING)


def main() -> None:
    load_dotenv(BASE_DIR / ".env")
    token = (os.getenv("BOT_TOKEN") or "").strip()
    if not token or "PASTE" in token.upper():
        print(
            "\n[!] Не задан токен бота!\n"
            "    Открой файл .env рядом с main.py и вставь токен от @BotFather:\n\n"
            "        BOT_TOKEN=1234567890:AA...\n"
        )
        sys.exit(1)

    setup_logging()
    logger.info("Запуск Minecraft News Bot…")

    app = Application.builder().token(token).post_init(post_init).build()

    app.add_handler(ChatMemberHandler(on_my_chat_member, ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(CommandHandler("start", cmd_start, filters=filters.ChatType.PRIVATE))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND, on_private_message))
    app.add_handler(CallbackQueryHandler(on_check_button, pattern=r"^check$"))
    app.add_error_handler(on_error)

    logger.info("Бот запущен. Жду сообщения…")
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
