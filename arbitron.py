#!/usr/bin/env python3
"""
Polymarket Inventory-Arb (buy-only) — LIVE or PAPER

Key features:
- Buy-only hedging (inventory build + completion)
- Uses Gamma "Get market by slug" to discover token IDs and tick size
- Uses Data API "Get positions" to compute hedged/unhedged live
- Rich UI + rotating debug log file
- Hard max spend cap per run (default $50)

Docs:
- Gamma: GET https://gamma-api.polymarket.com/markets/slug/{slug}
- Positions: GET https://data-api.polymarket.com/positions?user=...
"""

from __future__ import annotations

import argparse
import csv
from html import escape
from collections import deque
from email.utils import parsedate_to_datetime
import json
import logging
import math
import os
import re
import sys
import time
import threading
from types import SimpleNamespace
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from logging.handlers import RotatingFileHandler
from typing import Any, Dict, List, Optional, Tuple
from zoneinfo import ZoneInfo

import requests
from dotenv import load_dotenv
from rich import box
from rich.align import Align
from rich.console import Console, Group
from rich.layout import Layout
from rich.live import Live
from rich.panel import Panel
from rich.table import Table
from rich.text import Text
import websocket

# --- py-clob-client imports with compatibility guards ---
try:
    from py_clob_client.client import ClobClient
    from py_clob_client.clob_types import ApiCreds
    from py_clob_client.exceptions import PolyApiException
except Exception as e:  # pragma: no cover
    print("Missing dependency py-clob-client. Install: pip install py-clob-client")
    raise

# OrderArgs type differs across py-clob-client versions; keep a soft fallback.
try:
    from py_clob_client.clob_types import OrderArgs
except Exception:  # pragma: no cover
    OrderArgs = None  # type: ignore[assignment]

# BUY constant is not exported in some py-clob-client versions.
try:
    from py_clob_client.constants import BUY as BUY_SIDE
except Exception:  # pragma: no cover
    BUY_SIDE = "BUY"

try:
    from py_clob_client.constants import SELL as SELL_SIDE
except Exception:  # pragma: no cover
    SELL_SIDE = "SELL"

CHAINLINK_BTC_USD_FEED_POLYGON = "0xc907E116054Ad103354f2D350FD2514433D57F6f"
CHAINLINK_LATEST_ROUND_DATA_SELECTOR = "0xfeaf968c"
CHAINLINK_DECIMALS_SELECTOR = "0x313ce567"

# BOT_VERSION: update this whenever code changes so runtime and source can be cross-verified.
BOT_VERSION = "v2026.02.25.8"

# eth-account (usually installed via py-clob-client deps)
try:
    from eth_account import Account
except Exception as e:  # pragma: no cover
    Account = None


# ----------------------------
# Utilities
# ----------------------------

def now_utc() -> datetime:
    return datetime.now(timezone.utc)

def clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))

def parse_intish(s: Optional[str], default: int) -> int:
    if not s:
        return default
    m = re.search(r"-?\d+", s.strip())
    return int(m.group(0)) if m else default

def parse_floatish(s: Optional[str], default: float) -> float:
    if not s:
        return default
    m = re.search(r"-?\d+(\.\d+)?", s.strip())
    return float(m.group(0)) if m else default

def parse_boolish(s: Optional[str], default: bool) -> bool:
    if s is None:
        return default
    v = s.strip().lower()
    if v in {"1", "true", "t", "yes", "y", "on"}:
        return True
    if v in {"0", "false", "f", "no", "n", "off"}:
        return False
    return default

def fmt_money(x: float) -> str:
    return f"{x:,.4f}"

def fmt_toronto_hms(ts: float) -> str:
    if ts <= 0:
        return "-"
    try:
        return datetime.fromtimestamp(ts, tz=ZoneInfo("America/Toronto")).strftime("%H:%M:%S")
    except Exception:
        return "-"

def safe_addr(addr: Optional[str]) -> str:
    return addr or "∅"

def resolve_auth_params(signature_type: int, funder: Optional[str], logger: logging.Logger) -> Tuple[int, Optional[str], str]:
    """Normalize signature/funder config and emit helpful guidance."""
    mode_map = {0: "EOA", 1: "Proxy", 2: "Safe"}

    if signature_type not in (0, 1, 2):
        logger.warning("Unsupported signature_type=%s; defaulting to 0 (EOA).", signature_type)
        signature_type = 0

    funder = (funder or "").strip() or None

    if signature_type == 0 and funder:
        logger.info("signature_type=0 (EOA): ignoring funder=%s", funder)
        funder = None

    if signature_type in (1, 2) and not funder:
        logger.warning("signature_type=%s expects a proxy/safe funder address; missing funder may cause INVALID_SIGNATURE.", signature_type)

    return signature_type, funder, mode_map.get(signature_type, "Unknown")

def looks_like_privkey(k: str) -> bool:
    k = k.strip()
    if not k.startswith("0x"):
        return False
    return bool(re.fullmatch(r"0x[0-9a-fA-F]{64}", k))

POLYGON_USDC = "0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174"

def _rpc_hex_to_int(v: Any) -> Optional[int]:
    if not isinstance(v, str) or not v.startswith("0x"):
        return None
    try:
        return int(v, 16)
    except Exception:
        return None

def _rpc_call(rpc_url: str, method: str, params: List[Any], timeout: int = 8) -> Any:
    payload = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    r = requests.post(rpc_url, json=payload, timeout=timeout)
    r.raise_for_status()
    j = r.json()
    if isinstance(j, dict) and j.get("error"):
        raise RuntimeError(f"rpc_error={j['error']}")
    return j.get("result") if isinstance(j, dict) else None

def _erc20_balance_of_data(addr: str) -> str:
    a = addr.lower().replace("0x", "")
    return "0x70a08231" + ("0" * 24) + a

def parse_csv_urls(value: Optional[str]) -> List[str]:
    if not value:
        return []
    out: List[str] = []
    for part in value.split(","):
        u = part.strip()
        if u:
            out.append(u)
    return out

def best_from_book(book: Any) -> Tuple[Optional[float], Optional[float], Optional[float], Optional[float]]:
    """
    Returns: (best_bid_price, best_bid_size, best_ask_price, best_ask_size).

    Supports dict responses and py-clob-client model objects (e.g. OrderBookSummary).
    Computes true top-of-book from all levels (max bid / min ask) instead of assuming the
    first level is already sorted best-first.
    """

    def _pick(obj: Any, key: str) -> Any:
        if isinstance(obj, dict):
            return obj.get(key)
        return getattr(obj, key, None)

    def _to_float(raw: Any) -> Optional[float]:
        if raw is None:
            return None
        return parse_floatish(str(raw), default=None)

    def _levels(side: str) -> List[Tuple[float, float]]:
        raw = _pick(book, side)
        if not raw:
            return []

        out: List[Tuple[float, float]] = []

        # Some payloads can be dict(price->size), others list/tuple of level objects.
        if isinstance(raw, dict):
            iterable = [{"price": k, "size": v} for k, v in raw.items()]
        elif isinstance(raw, (list, tuple)):
            iterable = list(raw)
        else:
            iterable = [raw]

        for lvl in iterable:
            price = _to_float(_pick(lvl, "price"))
            size = _to_float(_pick(lvl, "size"))
            if price is None or size is None:
                continue
            out.append((price, size))
        return out

    bids = _levels("bids")
    asks = _levels("asks")

    bid_p, bid_s = (None, None)
    if bids:
        bid_p, bid_s = max(bids, key=lambda x: x[0])

    ask_p, ask_s = (None, None)
    if asks:
        ask_p, ask_s = min(asks, key=lambda x: x[0])

    # Some clients expose direct top-of-book summary fields.
    if bid_p is None:
        bid_p = _to_float(_pick(book, "best_bid") or _pick(book, "bestBid"))
    if ask_p is None:
        ask_p = _to_float(_pick(book, "best_ask") or _pick(book, "bestAsk"))
    if bid_s is None:
        bid_s = _to_float(_pick(book, "best_bid_size") or _pick(book, "bestBidSize"))
    if ask_s is None:
        ask_s = _to_float(_pick(book, "best_ask_size") or _pick(book, "bestAskSize"))

    return bid_p, bid_s, ask_p, ask_s


# ----------------------------
# Market discovery via Gamma
# ----------------------------

@dataclass
class MarketMeta:
    slug: str
    question: str
    outcomes: List[str]          # ["Up", "Down"]
    token_ids: List[str]         # clobTokenIds aligned to outcomes
    condition_id: str
    tick_size: float
    taker_fee_rate: float        # as fraction, e.g. 0.001 for 0.1%
    start_dt_utc: Optional[datetime]
    end_dt_utc: Optional[datetime]
    interval_s: int

def parse_jsonish_list(value: Any) -> List[Any]:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    if isinstance(value, str):
        s = value.strip()
        # try JSON
        try:
            v = json.loads(s)
            if isinstance(v, list):
                return v
        except Exception:
            pass
        # try comma-separated
        if "," in s:
            return [x.strip() for x in s.split(",") if x.strip()]
        # try single token
        if s:
            return [s]
    return []

def infer_interval_from_slug(slug: str) -> int:
    """
    Tries to infer interval seconds from slug patterns like:
    btc-updown-5m-1771376400
    btc-updown-15m-1771376400
    """
    m = re.search(r"-(\d+)m-(\d{9,12})$", slug)
    if m:
        mins = int(m.group(1))
        return mins * 60
    return 300

def infer_start_ts_from_slug(slug: str) -> Optional[int]:
    m = re.search(r"-(\d{9,12})$", slug)
    return int(m.group(1)) if m else None

def current_symbol_5m_slug(symbol: str, now: Optional[datetime] = None) -> str:
    now_utc = now.astimezone(timezone.utc) if now else datetime.now(timezone.utc)
    ts = int(now_utc.timestamp())
    start_ts = (ts // 300) * 300
    sym = (symbol or "btc").strip().lower()
    return f"{sym}-updown-5m-{start_ts}"


def current_btc_5m_slug(now: Optional[datetime] = None) -> str:
    return current_symbol_5m_slug("btc", now)


def choose_symbol_slug(gamma_host: str, logger: logging.Logger, symbol: str, now: Optional[datetime] = None) -> str:
    sym = (symbol or "btc").strip().lower()
    candidates = fetch_current_crypto_5m_slugs(gamma_host, logger, now)
    prefix = f"{sym}-updown-5m-"
    for slug in candidates:
        if slug.startswith(prefix):
            return slug
    return current_symbol_5m_slug(sym, now)


def fetch_current_crypto_5m_slugs(gamma_host: str, logger: logging.Logger, now: Optional[datetime] = None) -> List[str]:
    """Discover current 5m up/down crypto slugs from Gamma and include BTC fallback."""
    now_utc = now.astimezone(timezone.utc) if now else datetime.now(timezone.utc)
    start_ts = (int(now_utc.timestamp()) // 300) * 300
    url = f"{gamma_host.rstrip('/')}/markets"

    rows: List[dict] = []

    # Gamma responses can be paginated; gather multiple pages to avoid only seeing BTC.
    for page in range(0, 6):
        offset = page * 500
        page_rows: List[dict] = []
        for params in (
            {"active": "true", "closed": "false", "limit": 500, "offset": offset},
            {"limit": 500, "offset": offset},
            {"offset": offset},
        ):
            try:
                r = requests.get(url, params=params, timeout=8)
                if not r.ok:
                    continue
                payload = r.json()
                if isinstance(payload, list):
                    page_rows = payload
                elif isinstance(payload, dict):
                    page_rows = payload.get("data") or payload.get("markets") or payload.get("rows") or []
                if page_rows:
                    break
            except Exception:
                continue
        if not page_rows:
            break
        rows.extend([x for x in page_rows if isinstance(x, dict)])
        if len(page_rows) < 500:
            break

    out: List[str] = []
    for row in rows:
        slug = str(row.get("slug") or "").strip().lower()
        if not slug or "-updown-5m-" not in slug:
            continue
        ts = infer_start_ts_from_slug(slug)
        interval = infer_interval_from_slug(slug)
        if ts is None or interval != 300:
            continue
        # Accept slugs within current/adjacent 5m bucket to avoid missing near-boundary listings.
        if abs(ts - start_ts) <= 300:
            out.append(slug)

    out = sorted(dict.fromkeys(out))
    btc_slug = current_btc_5m_slug(now_utc)
    if btc_slug not in out:
        out.insert(0, btc_slug)
    if len(out) <= 1:
        logger.info("Crypto 5m discovery found %s slug(s). Using fallback BTC if needed.", len(out))
    else:
        logger.info("Crypto 5m discovery found %s slug(s).", len(out))
    return out


def choose_best_slug_by_ask_sum(gamma_host: str, public_client: ClobClient, logger: logging.Logger, now: Optional[datetime] = None) -> str:
    """Pick the current 5m crypto slug with the lowest UP+DOWN ask sum."""
    candidates = fetch_current_crypto_5m_slugs(gamma_host, logger, now)
    best_slug = candidates[0] if candidates else current_btc_5m_slug(now)
    best_sum = 1e9

    for slug in candidates:
        try:
            meta = fetch_market_meta(gamma_host, slug, logger)
            if len(meta.token_ids) < 2:
                continue
            up_book = public_client.get_order_book(meta.token_ids[0])
            dn_book = public_client.get_order_book(meta.token_ids[1])
            _, _, up_ask, _ = best_from_book(up_book)
            _, _, dn_ask, _ = best_from_book(dn_book)
            if up_ask is None or dn_ask is None:
                continue
            ask_sum = up_ask + dn_ask
            if ask_sum < best_sum:
                best_sum = ask_sum
                best_slug = slug
        except Exception:
            continue

    return best_slug

def shift_slug_by_intervals(slug: str, steps: int) -> str:
    ts = infer_start_ts_from_slug(slug)
    if ts is None:
        return slug
    interval = infer_interval_from_slug(slug)
    prefix = re.sub(r"-\d{9,12}$", "", slug)
    return f"{prefix}-{ts + (steps * interval)}"

def normalize_slug_input(value: str) -> str:
    """Accept either raw slug or full polymarket event URL and return the slug."""
    s = (value or "").strip()
    if not s:
        return s
    # Example: https://polymarket.com/event/btc-updown-5m-1771378800
    m = re.search(r"/event/([^/?#]+)", s)
    if m:
        return m.group(1)
    return s


def build_slug_candidates(seed_slug: str, *, back: int = 5, forward: int = 12) -> List[Tuple[str, Optional[datetime]]]:
    """
    Build nearby slug candidates around a seed slug using interval/timestamp patterns.
    Returns tuples of (slug, start_dt_utc).
    """
    seed_slug = normalize_slug_input(seed_slug)
    ts = infer_start_ts_from_slug(seed_slug)
    if ts is None:
        return [(seed_slug, None)]

    interval_s = infer_interval_from_slug(seed_slug)
    prefix = re.sub(r"-\d{9,12}$", "", seed_slug)

    out: List[Tuple[str, Optional[datetime]]] = []
    for i in range(-back, forward + 1):
        t = ts + (i * interval_s)
        cand = f"{prefix}-{t}"
        out.append((cand, datetime.fromtimestamp(t, tz=timezone.utc)))
    return out


def build_current_upcoming_slug_candidates(seed_slug: str, *, now: Optional[datetime] = None) -> List[Tuple[str, Optional[datetime]]]:
    """
    Build a tight menu containing only:
      1) the current interval slug (started within the last interval), and
      2) the upcoming interval slug (next interval).

    If parsing fails, falls back to the seed slug only.
    """
    seed_slug = normalize_slug_input(seed_slug)
    ts = infer_start_ts_from_slug(seed_slug)
    if ts is None:
        return [(seed_slug, None)]

    interval_s = infer_interval_from_slug(seed_slug)
    prefix = re.sub(r"-\d{9,12}$", "", seed_slug)
    now_utc = now.astimezone(timezone.utc) if now else datetime.now(timezone.utc)
    now_ts = int(now_utc.timestamp())

    current_start_ts = (now_ts // interval_s) * interval_s
    upcoming_start_ts = current_start_ts + interval_s

    current_slug = f"{prefix}-{current_start_ts}"
    upcoming_slug = f"{prefix}-{upcoming_start_ts}"

    return [
        (current_slug, datetime.fromtimestamp(current_start_ts, tz=timezone.utc)),
        (upcoming_slug, datetime.fromtimestamp(upcoming_start_ts, tz=timezone.utc)),
    ]


def select_slug_interactive(console: Console, candidates: List[Tuple[str, Optional[datetime]]]) -> Optional[str]:
    """
    Keyboard picker: Up/Down to move, Enter to select, q to cancel.
    Works on Windows and Unix terminals.
    """
    if not candidates:
        return None

    idx = 0

    def _render() -> None:
        console.clear()
        tbl = Table(title="Select market slug", box=box.ROUNDED, expand=True)
        tbl.add_column(" ", justify="center", width=3)
        tbl.add_column("Type", justify="center", width=10)
        tbl.add_column("Slug", overflow="fold")
        tbl.add_column("Start (local)", justify="right")
        tbl.add_column("Start (UTC)", justify="right")

        for i, (slug, dt_utc) in enumerate(candidates):
            marker = "➤" if i == idx else " "
            label = ""
            if i == 0:
                label = "(CURRENT)"
            elif i == 1:
                label = "(UPCOMING)"
            if dt_utc is None:
                local_s = "-"
                utc_s = "-"
            else:
                local_s = dt_utc.astimezone().strftime("%Y-%m-%d %H:%M:%S")
                utc_s = dt_utc.strftime("%Y-%m-%d %H:%M:%S")
            row_style = "bold white on dark_green" if i == idx else ""
            tbl.add_row(marker, label, slug, local_s, utc_s, style=row_style)

        help_txt = Text("Use ↑/↓ to move, Enter to select, q to cancel", style="bold cyan")
        console.print(Panel(Group(tbl, Align.center(help_txt)), title="Polymarket Slug Picker", box=box.ROUNDED))

    def _read_key() -> str:
        if os.name == "nt":
            import msvcrt  # type: ignore

            ch = msvcrt.getwch()
            if ch in ("\x00", "\xe0"):
                ch2 = msvcrt.getwch()
                if ch2 == "H":
                    return "up"
                if ch2 == "P":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            return "other"

        import termios
        import tty

        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            ch = sys.stdin.read(1)
            if ch == "\x1b":
                c2 = sys.stdin.read(1)
                c3 = sys.stdin.read(1)
                seq = ch + c2 + c3
                if seq == "\x1b[A":
                    return "up"
                if seq == "\x1b[B":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            return "other"
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)

    while True:
        _render()
        k = _read_key()
        if k == "up":
            idx = (idx - 1) % len(candidates)
        elif k == "down":
            idx = (idx + 1) % len(candidates)
        elif k == "enter":
            console.clear()
            return candidates[idx][0]
        elif k == "quit":
            console.clear()
            return None


def select_market_symbol_interactive(console: Console) -> Optional[str]:
    """Simple selector for 5m crypto markets at startup."""
    options = [
        ("btc", "Bitcoin (BTC)"),
        ("eth", "Ethereum (ETH)"),
        ("sol", "Solana (SOL)"),
        ("xrp", "XRP (XRP)"),
    ]
    idx = 0

    def _read_key() -> str:
        if os.name == "nt":
            import msvcrt  # type: ignore

            ch = msvcrt.getwch()
            if ch in ("\x00", "\xe0"):
                ch2 = msvcrt.getwch()
                if ch2 == "H":
                    return "up"
                if ch2 == "P":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            return "other"

        import termios
        import tty

        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            ch = sys.stdin.read(1)
            if ch == "\x1b":
                c2 = sys.stdin.read(1)
                c3 = sys.stdin.read(1)
                seq = ch + c2 + c3
                if seq == "\x1b[A":
                    return "up"
                if seq == "\x1b[B":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            return "other"
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)

    while True:
        console.clear()
        tbl = Table(title="Select market", box=box.ROUNDED, expand=True)
        tbl.add_column(" ", width=3, justify="center")
        tbl.add_column("Market", justify="left")
        for i, (_, label) in enumerate(options):
            marker = "▶" if i == idx else " "
            row_style = "bold white on dark_green" if i == idx else ""
            tbl.add_row(marker, label, style=row_style)
        help_txt = Text("Use ↑/↓ to move, Enter to select, q to keep BTC", style="bold cyan")
        console.print(Panel(Group(tbl, Align.center(help_txt)), title="5m Crypto Market", box=box.ROUNDED))

        k = _read_key()
        if k == "up":
            idx = (idx - 1) % len(options)
        elif k == "down":
            idx = (idx + 1) % len(options)
        elif k == "enter":
            console.clear()
            return options[idx][0]
        elif k == "quit":
            console.clear()
            return None

def select_strategy_mode_interactive(console: Console) -> Optional[str]:
    """Popup selector for startup strategy mode."""
    options = [
        ("scalp", "Penny Scalping", "Spot brief oscillations and target +$0.01 exits"),
        ("arb", "Original Arbitrage", "Use instant bundle/completion/inventory arbitrage logic"),
        ("hedge", "Quant Hedge", "Target near-draw payoff with capped downside and selective upside adds"),
        ("gpt", "GPT Mode", "Blend live BTC momentum + market microstructure for adaptive directional sizing"),
        ("fortress", "Fortress Buy-Hedge", "Buy-only market-neutral core with bounded directional tilt"),
        ("upswing", "Upswing Penny Scalper", "Ride clear micro-upswings with TP/SL exits"),
        ("ml", "ML Lab (paper)", "Adaptive virtual-wallet strategy search (no real orders)"),
        ("replicate", "Replication Mode", "Late-window paired buys with fixed cadence + bounded imbalance"),
        ("collect", "Data Collector", "No trading: capture market + BTC tick data for offline AI analysis"),
    ]
    idx = 0

    def _read_key() -> str:
        if os.name == "nt":
            import msvcrt  # type: ignore

            ch = msvcrt.getwch()
            if ch in ("\x00", "\xe0"):
                ch2 = msvcrt.getwch()
                if ch2 == "H":
                    return "up"
                if ch2 == "P":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            return "other"

        import termios
        import tty

        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            ch = sys.stdin.read(1)
            if ch == "\x1b":
                c2 = sys.stdin.read(1)
                c3 = sys.stdin.read(1)
                seq = ch + c2 + c3
                if seq == "\x1b[A":
                    return "up"
                if seq == "\x1b[B":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            return "other"
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)

    while True:
        console.clear()
        tbl = Table(title="Select startup strategy", box=box.ROUNDED, expand=True)
        tbl.add_column(" ", width=3, justify="center")
        tbl.add_column("Mode", justify="left")
        tbl.add_column("Description", justify="left")
        for i, (_, label, desc) in enumerate(options):
            marker = "➤" if i == idx else " "
            row_style = "bold white on dark_blue" if i == idx else ""
            tbl.add_row(marker, label, desc, style=row_style)
        help_txt = Text("Use ↑/↓ then Enter (q to cancel)", style="bold cyan")
        console.print(Panel(Group(tbl, Align.center(help_txt)), title="Strategy Mode", box=box.ROUNDED))
        k = _read_key()
        if k == "up":
            idx = (idx - 1) % len(options)
        elif k == "down":
            idx = (idx + 1) % len(options)
        elif k == "enter":
            console.clear()
            return options[idx][0]
        elif k == "quit":
            console.clear()
            return None


def select_scalp_settings_interactive(console: Console, args: argparse.Namespace) -> None:
    """Prompt for optional penny-scalp runtime overrides after scalp mode is chosen."""
    console.clear()
    defaults = [
        ("max_trades", "Max total trades this run (buy+sell, 0 = unlimited)", float(args.max_trades)),
        ("step", "Max shares per trade", float(args.step)),
        ("max_session_shares", "Max shares per market session", float(args.max_session_shares)),
        ("max_spend", "Max spend USD", float(args.max_spend)),
    ]

    tbl = Table(title="Penny Scalping Runtime Settings", box=box.ROUNDED, expand=True)
    tbl.add_column("Setting", justify="left")
    tbl.add_column("Current", justify="right")
    tbl.add_column("How to edit", justify="left")
    for _, label, value in defaults:
        tbl.add_row(label, f"{value:g}", "Type a number then Enter, or press Enter to keep")
    console.print(Panel(tbl, title="Scalp Settings", box=box.ROUNDED))

    def _ask_float(prompt: str, current: float, lo: float) -> float:
        raw = console.input(f"[bold cyan]{prompt}[/bold cyan] [dim](current {current:g})[/dim]: ").strip()
        if not raw:
            return current
        v = parse_floatish(raw, current)
        return max(lo, v)

    args.max_trades = int(_ask_float("Max total trades this run (buy+sell, 0 = unlimited)", float(args.max_trades), 0.0))
    args.step = _ask_float("Max shares per trade", float(args.step), 0.1)
    args.max_session_shares = _ask_float("Max shares per market session", float(args.max_session_shares), 1.0)
    args.max_spend = _ask_float("Max spend USD", float(args.max_spend), 1.0)

    summary = Table.grid(padding=(0, 1))
    summary.add_column(justify="right", style="bold")
    summary.add_column(justify="left")
    summary.add_row("Max total trades", str(args.max_trades))
    summary.add_row("Shares / trade", f"{args.step:g}")
    summary.add_row("Session share cap", f"{args.max_session_shares:g}")
    summary.add_row("Max spend USD", f"{args.max_spend:g}")
    console.print(Panel(summary, title="Scalp settings applied", box=box.ROUNDED))
    time.sleep(0.8)
    console.clear()


def select_upswing_settings_interactive(console: Console, args: argparse.Namespace) -> None:
    """Prompt for optional upswing-scalp runtime overrides."""
    console.clear()
    tbl = Table(title="Upswing Scalper Runtime Settings", box=box.ROUNDED, expand=True)
    tbl.add_column("Setting", justify="left")
    tbl.add_column("Current", justify="right")
    tbl.add_column("How to edit", justify="left")
    rows = [
        ("max_trades", "Max total trades this run (buy+sell, 0 = unlimited)", float(args.max_trades)),
        ("step", "Max shares per trade", float(args.step)),
        ("max_session_shares", "Max shares per market session", float(args.max_session_shares)),
        ("max_spend", "Max spend USD", float(args.max_spend)),
        ("upswing_take_profit_cents", "Take profit cents", float(args.upswing_take_profit_cents)),
        ("upswing_stop_loss_cents", "Stop loss cents", float(args.upswing_stop_loss_cents)),
    ]
    for _, label, value in rows:
        tbl.add_row(label, f"{value:g}", "Type a number then Enter, or press Enter to keep")
    console.print(Panel(tbl, title="Upswing Scalper", box=box.ROUNDED))

    def _ask_float(prompt: str, current: float, lo: float) -> float:
        raw = console.input(f"[bold cyan]{prompt}[/bold cyan] [dim](current {current:g})[/dim]: ").strip()
        if not raw:
            return current
        return max(lo, parse_floatish(raw, current))

    args.max_trades = int(_ask_float("Max total trades this run (buy+sell, 0 = unlimited)", float(args.max_trades), 0.0))
    args.step = _ask_float("Max shares per trade", float(args.step), 0.1)
    args.max_session_shares = _ask_float("Max shares per market session", float(args.max_session_shares), 1.0)
    args.max_spend = _ask_float("Max spend USD", float(args.max_spend), 1.0)
    args.upswing_take_profit_cents = _ask_float("Take profit cents", float(args.upswing_take_profit_cents), 0.005)
    args.upswing_stop_loss_cents = _ask_float("Stop loss cents", float(args.upswing_stop_loss_cents), 0.005)

    console.print(Panel("Upswing settings applied.", title="Upswing Scalper", box=box.ROUNDED))
    time.sleep(0.8)
    console.clear()


def select_hedge_settings_interactive(console: Console, args: argparse.Namespace) -> None:
    """Prompt for quant-hedge runtime overrides after hedge mode is chosen."""
    console.clear()
    tbl = Table(title="Quant Hedge Runtime Settings", box=box.ROUNDED, expand=True)
    tbl.add_column("Setting", justify="left")
    tbl.add_column("Current", justify="right")
    tbl.add_column("Notes", justify="left")
    tbl.add_row("Max total trades", f"{args.max_trades:g}", "0 = unlimited")
    tbl.add_row("Max shares per trade", f"{args.step:g}", "Per entry cap")
    tbl.add_row("Max shares per session", f"{args.max_session_shares:g}", "Total BUY cap")
    tbl.add_row("Max spend USD", f"{args.max_spend:g}", "Run-level budget")
    tbl.add_row("Minor-loss cap (USD)", f"{args.hedge_minor_loss_limit:g}", "Target worst-case settlement >= -cap")
    tbl.add_row("Upside allocation", f"{args.hedge_upside_allocation:g}", "Fraction of safety buffer usable for directional adds")
    tbl.add_row("Max upside shares", f"{args.hedge_max_extra_shares:g}", "Cap per upside add")
    console.print(Panel(tbl, title="Hedge Settings", box=box.ROUNDED))

    def _ask(prompt: str, cur: float, lo: float) -> float:
        raw = console.input(f"[bold cyan]{prompt}[/bold cyan] [dim](current {cur:g})[/dim]: ").strip()
        if not raw:
            return cur
        return max(lo, parse_floatish(raw, cur))

    args.max_trades = int(_ask("Max total trades this run (buy+sell, 0 = unlimited)", float(args.max_trades), 0.0))
    args.step = _ask("Max shares per trade", float(args.step), 0.1)
    args.max_session_shares = _ask("Max shares per market session", float(args.max_session_shares), 1.0)
    args.max_spend = _ask("Max spend USD", float(args.max_spend), 1.0)
    args.hedge_minor_loss_limit = _ask("Minor-loss cap USD", float(args.hedge_minor_loss_limit), 0.0)
    args.hedge_upside_allocation = min(1.0, _ask("Upside allocation (0-1)", float(args.hedge_upside_allocation), 0.0))
    args.hedge_max_extra_shares = _ask("Max upside shares per add", float(args.hedge_max_extra_shares), 0.1)
    console.print(Panel("Hedge settings applied.", title="Quant Hedge", box=box.ROUNDED))
    time.sleep(0.8)
    console.clear()


def select_gpt_settings_interactive(console: Console, args: argparse.Namespace) -> None:
    """Prompt for GPT-mode runtime overrides after GPT mode is chosen."""
    console.clear()
    tbl = Table(title="GPT Mode Runtime Settings", box=box.ROUNDED, expand=True)
    tbl.add_column("Setting", justify="left")
    tbl.add_column("Current", justify="right")
    tbl.add_column("Notes", justify="left")
    tbl.add_row("Max spend USD", f"{args.max_spend:g}", "Budget upper bound")
    tbl.add_row("Max total trades", f"{args.max_trades:g}", "0 = unlimited")
    tbl.add_row("Max shares per trade", f"{args.step:g}", "Per entry cap")
    tbl.add_row("Max shares per session", f"{args.max_session_shares:g}", "Session risk cap")
    tbl.add_row("GPT alloc fraction", f"{args.gpt_alloc_fraction:g}", "Fraction of remaining budget per signal")
    tbl.add_row("GPT min signal", f"{args.gpt_min_signal:g}", "Higher = fewer but stronger bets")
    console.print(Panel(tbl, title="GPT Settings", box=box.ROUNDED))

    def _ask(prompt: str, cur: float, lo: float) -> float:
        raw = console.input(f"[bold cyan]{prompt}[/bold cyan] [dim](current {cur:g})[/dim]: ").strip()
        if not raw:
            return cur
        return max(lo, parse_floatish(raw, cur))

    args.max_spend = _ask("Max spend USD", float(args.max_spend), 1.0)
    args.max_trades = int(_ask("Max total trades this run (buy+sell, 0=unlimited)", float(args.max_trades), 0.0))
    args.step = _ask("Max shares per trade", float(args.step), 0.1)
    args.max_session_shares = _ask("Max shares per market session", float(args.max_session_shares), 1.0)
    args.gpt_alloc_fraction = min(1.0, _ask("GPT allocation fraction (0-1)", float(args.gpt_alloc_fraction), 0.01))
    args.gpt_min_signal = min(1.0, _ask("GPT minimum signal strength (0-1)", float(args.gpt_min_signal), 0.01))

    console.print(Panel("GPT mode settings applied.", title="GPT Mode", box=box.ROUNDED))
    time.sleep(0.8)
    console.clear()


def select_fortress_settings_interactive(console: Console, args: argparse.Namespace) -> None:
    """Prompt for buy-only fortress runtime overrides."""
    console.clear()
    tbl = Table(title="Fortress Buy-Hedge Settings", box=box.ROUNDED, expand=True)
    tbl.add_column("Setting", justify="left")
    tbl.add_column("Current", justify="right")
    tbl.add_column("Notes", justify="left")
    tbl.add_row("Max spend USD", f"{args.max_spend:g}", "Total budget")
    tbl.add_row("Max total trades", f"{args.max_trades:g}", "0 = unlimited")
    tbl.add_row("Max shares per trade", f"{args.step:g}", "Per action")
    tbl.add_row("Max shares per session", f"{args.max_session_shares:g}", "Session cap")
    tbl.add_row("Loss cap USD", f"{args.fortress_loss_cap:g}", "Guard worst-case settlement")
    tbl.add_row("Pair lock edge", f"{args.fortress_lock_edge:g}", "Need this edge to buy both sides")
    tbl.add_row("Tilt budget frac", f"{args.fortress_tilt_budget:g}", "Use only this cushion for directional adds")
    tbl.add_row("Max imbalance shares", f"{args.fortress_max_imbalance:g}", "Directional risk cap")
    tbl.add_row("Max tilt shares", f"{args.fortress_max_tilt_shares:g}", "Per tilt action")
    console.print(Panel(tbl, title="Fortress Mode", box=box.ROUNDED))

    def _ask(prompt: str, cur: float, lo: float) -> float:
        raw = console.input(f"[bold cyan]{prompt}[/bold cyan] [dim](current {cur:g})[/dim]: ").strip()
        if not raw:
            return cur
        return max(lo, parse_floatish(raw, cur))

    args.max_spend = _ask("Max spend USD", float(args.max_spend), 1.0)
    args.max_trades = int(_ask("Max total trades (0=unlimited)", float(args.max_trades), 0.0))
    args.step = _ask("Max shares per trade", float(args.step), 0.1)
    args.max_session_shares = _ask("Max shares per market session", float(args.max_session_shares), 1.0)
    args.fortress_loss_cap = _ask("Loss cap USD", float(args.fortress_loss_cap), 0.0)
    args.fortress_lock_edge = _ask("Pair lock edge", float(args.fortress_lock_edge), 0.0)
    args.fortress_tilt_budget = min(1.0, _ask("Tilt budget fraction (0-1)", float(args.fortress_tilt_budget), 0.0))
    args.fortress_max_imbalance = _ask("Max imbalance shares", float(args.fortress_max_imbalance), 0.1)
    args.fortress_max_tilt_shares = _ask("Max tilt shares", float(args.fortress_max_tilt_shares), 0.1)

    console.print(Panel("Fortress settings applied.", title="Fortress Mode", box=box.ROUNDED))
    time.sleep(0.8)
    console.clear()


def select_arb_settings_interactive(console: Console, args: argparse.Namespace) -> None:
    """Per-setting risk-level selector for classic arbitrage startup tuning."""
    cfg_path = Path(".arb_last_config.json")

    def _read_key() -> str:
        if os.name == "nt":
            import msvcrt  # type: ignore

            ch = msvcrt.getwch()
            if ch in ("\x00", "\xe0"):
                ch2 = msvcrt.getwch()
                if ch2 == "H":
                    return "up"
                if ch2 == "P":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            if ch.lower() == "s":
                return "skip"
            return "other"

        import termios
        import tty

        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            ch = sys.stdin.read(1)
            if ch == "\x1b":
                c2 = sys.stdin.read(1)
                c3 = sys.stdin.read(1)
                seq = ch + c2 + c3
                if seq == "\x1b[A":
                    return "up"
                if seq == "\x1b[B":
                    return "down"
                return "other"
            if ch in ("\r", "\n"):
                return "enter"
            if ch.lower() == "q":
                return "quit"
            if ch.lower() == "s":
                return "skip"
            return "other"
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)

    level_labels_by_count: Dict[int, List[str]] = {
        4: ["Low", "Medium", "High", "Highest"],
        5: ["Lowest", "Low", "Medium", "High", "Highest"],
        6: ["Lowest", "Low", "Medium", "High", "Higher", "Highest"],
    }
    settings: List[Dict[str, Any]] = [
        {
            "name": "Min edge",
            "attr": "min_edge",
            "values": [0.008, 0.006, 0.004, 0.0025, 0.0015],
            "fmt": lambda v: f"{float(v):.4f}",
            "note": "Higher = safer/fewer buys",
        },
        {
            "name": "Shares per trade",
            "attr": "step",
            "values": [5.0, 10.0, 15.0, 20.0, 25.0],
            "fmt": lambda v: f"{float(v):.0f}",
            "note": "Per-action max shares",
        },
        {
            "name": "Max session shares",
            "attr": "max_session_shares",
            "values": [10.0, 20.0, 30.0, 40.0, 50.0, 60.0],
            "fmt": lambda v: f"{float(v):.0f}",
            "note": "Total buy shares per market",
        },
        {
            "name": "Max trades",
            "attr": "max_trades",
            "values": [80, 40, 0, 0, 0],
            "fmt": lambda v: ("∞" if int(v) == 0 else str(int(v))),
            "note": "0 = unlimited",
        },
        {
            "name": "Post-open wait",
            "attr": "market_open_delay_s",
            "values": [5, 10, 15, 30],
            "fmt": lambda v: f"{int(v)}s",
            "note": "Wait this long after market open before buying",
        },
        {
            "name": "Allow inventory build",
            "attr": "allow_inventory_build",
            "values": [False, False, False, True, True],
            "fmt": lambda v: ("on" if bool(v) else "off"),
            "note": "One-sided build when bundle unavailable",
        },
        {
            "name": "Max net imbalance",
            "attr": "max_net_imbalance_shares",
            "values": [0.5, 1.0, 1.5, 2.5, 4.0],
            "fmt": lambda v: f"{float(v):.1f}",
            "note": "|UP-DOWN| exposure cap",
        },
        {
            "name": "Poll interval",
            "attr": "poll",
            "values": [0.60, 0.50, 0.35, 0.25, 0.15],
            "fmt": lambda v: f"{float(v):.2f}s",
            "note": "Lower = faster/more requests",
        },
        {
            "name": "Aggressive edge relax",
            "attr": "aggressive_edge_relax",
            "values": [False, False, True, True, True],
            "fmt": lambda v: ("on" if bool(v) else "off"),
            "note": "Relaxes edge faster after dry spells",
        },
    ]

    defaults_map: Dict[str, Any] = {st["attr"]: getattr(args, st["attr"]) for st in settings}
    saved_map: Dict[str, Any] = {}
    try:
        if cfg_path.exists():
            loaded = json.loads(cfg_path.read_text(encoding="utf-8"))
            if isinstance(loaded, dict):
                saved_map = loaded
    except Exception:
        saved_map = {}

    used_saved_fastpath = False

    def _apply_map(source: Dict[str, Any]):
        for st in settings:
            attr = st["attr"]
            if attr in source:
                setattr(args, attr, source[attr])

    for st in settings:
        attr = st["attr"]
        vals = st["values"]
        cur = saved_map.get(attr, getattr(args, attr))
        if isinstance(cur, bool):
            idx = vals.index(cur) if cur in vals else 0
        else:
            try:
                idx = min(range(len(vals)), key=lambda i: abs(float(vals[i]) - float(cur)))
            except Exception:
                idx = 1

        while True:
            console.clear()
            tbl = Table(title=f"Classic Arbitrage: {st['name']}", box=box.ROUNDED, expand=True)
            tbl.add_column(" ", width=3, justify="center")
            tbl.add_column("Risk level", justify="left")
            tbl.add_column("Value", justify="left")
            level_labels = level_labels_by_count.get(len(vals), [f"Option {i+1}" for i in range(len(vals))])
            for i, lvl in enumerate(level_labels):
                marker = "➤" if i == idx else " "
                row_style = "bold white on dark_blue" if i == idx else ""
                tbl.add_row(marker, lvl, st["fmt"](vals[i]), style=row_style)
            hint = Text(f"{st['note']}\nUse ↑/↓ then Enter (q keeps current)", style="bold cyan")
            if saved_map:
                hint = Text(f"{st['note']}\nUse ↑/↓ then Enter (q keeps current, s=use last saved config now)", style="bold cyan")
            console.print(Panel(Group(tbl, Align.center(hint)), title="Classic Arbitrage", box=box.ROUNDED))
            k = _read_key()
            if k == "up":
                idx = (idx - 1) % len(vals)
            elif k == "down":
                idx = (idx + 1) % len(vals)
            elif k == "enter":
                setattr(args, attr, vals[idx])
                break
            elif k == "quit":
                break
            elif k == "skip":
                _apply_map(saved_map if saved_map else defaults_map)
                used_saved_fastpath = True
                break

        if used_saved_fastpath:
            break

    try:
        to_save = {st["attr"]: getattr(args, st["attr"]) for st in settings}
        cfg_path.write_text(json.dumps(to_save, indent=2, sort_keys=True), encoding="utf-8")
    except Exception:
        pass

    console.print(
        Panel(
            (
                f"Applied classic-arb settings:\n"
                f"min_edge={args.min_edge:.4f} step={args.step:g} max_session_shares={args.max_session_shares:g} "
                f"max_trades={'∞' if args.max_trades == 0 else args.max_trades} post_open_wait={int(args.market_open_delay_s)}s allow_inventory_build={args.allow_inventory_build} "
                f"max_net_imbalance={args.max_net_imbalance_shares:g} poll={args.poll:.2f}s aggressive_edge_relax={args.aggressive_edge_relax}\n"
                f"saved_config={cfg_path}"
            ),
            title="Classic Arbitrage",
            box=box.ROUNDED,
        )
    )
    time.sleep(0.8)
    console.clear()


def fetch_market_meta(gamma_host: str, slug: str, logger: logging.Logger) -> MarketMeta:
    url = f"{gamma_host.rstrip('/')}/markets/slug/{slug}"
    r = requests.get(url, timeout=10)
    r.raise_for_status()
    mkt = r.json()

    question = str(mkt.get("question") or "")
    condition_id = str(mkt.get("conditionId") or "")

    outcomes = parse_jsonish_list(mkt.get("outcomes"))
    token_ids = parse_jsonish_list(mkt.get("clobTokenIds"))

    # Tick size: docs show orderPriceMinTickSize field
    tick_size = parse_floatish(str(mkt.get("orderPriceMinTickSize")), default=0.01)
    if tick_size <= 0:
        tick_size = 0.01

    # Fee: docs expose takerBaseFee; sometimes fee is string/number
    # Treat as "basis points"?? It's not consistently documented in Gamma response,
    # so we keep it conservative and also allow override via env/cli.
    taker_base_fee = mkt.get("takerBaseFee")
    taker_fee_rate = 0.0
    if taker_base_fee is not None:
        # If takerBaseFee looks like 1000 meaning 0.1% in "cppm", rate = 1000 / 1_000_000
        # If it looks like 10 meaning 1%?? unclear; we handle both with heuristic.
        x = float(taker_base_fee)
        if x > 1 and x <= 1000000:
            # assume cppm
            taker_fee_rate = x / 1_000_000.0
        elif 0 < x < 1:
            taker_fee_rate = x
        else:
            taker_fee_rate = 0.0

    interval_s = infer_interval_from_slug(slug)
    start_ts = infer_start_ts_from_slug(slug)
    start_dt = datetime.fromtimestamp(start_ts, tz=timezone.utc) if start_ts else None
    end_dt = (start_dt + timedelta(seconds=interval_s)) if start_dt else None  # type: ignore[name-defined]

    # Fallback: gamma endDate is an ISO string
    # For these 5m markets, slug timestamp tends to be the start; end = start + interval.
    # But if end_dt is missing, use gamma endDate.
    if end_dt is None and mkt.get("endDate"):
        try:
            # endDate example ends with Z
            end_dt = datetime.fromisoformat(str(mkt["endDate"]).replace("Z", "+00:00"))
        except Exception:
            end_dt = None

    if start_dt is None and mkt.get("startDate"):
        try:
            start_dt = datetime.fromisoformat(str(mkt["startDate"]).replace("Z", "+00:00"))
        except Exception:
            start_dt = None

    # Normalize order: outcomes and token ids should align.
    # For Up/Down markets it’s usually exactly 2.
    if len(outcomes) != len(token_ids) or len(outcomes) < 2:
        logger.warning("Gamma returned outcomes/tokenIds mismatch. outcomes=%s token_ids=%s", outcomes, token_ids)

    # Force to first two if more than 2
    outcomes = [str(x) for x in outcomes][:2]
    token_ids = [str(x) for x in token_ids][:2]

    return MarketMeta(
        slug=slug,
        question=question,
        outcomes=outcomes,
        token_ids=token_ids,
        condition_id=condition_id,
        tick_size=tick_size,
        taker_fee_rate=taker_fee_rate,
        start_dt_utc=start_dt,
        end_dt_utc=end_dt,
        interval_s=interval_s,
    )


# ----------------------------
# Positions via Data API
# ----------------------------

@dataclass
class PositionRow:
    outcome: str
    size: float
    avg_price: float

@dataclass
class PositionSnapshot:
    up: PositionRow
    down: PositionRow

    @property
    def hedged(self) -> float:
        return min(self.up.size, self.down.size)

    @property
    def unhedged_up(self) -> float:
        return max(0.0, self.up.size - self.hedged)

    @property
    def unhedged_down(self) -> float:
        return max(0.0, self.down.size - self.hedged)

def fetch_positions(data_api_host: str, user_addr: str, condition_id: str, logger: logging.Logger) -> PositionSnapshot:
    """
    Uses Data API positions to get current outcome token holdings.
    Docs: GET https://data-api.polymarket.com/positions?user=...&market=...
    The "market" query param is comma-separated condition IDs. :contentReference[oaicite:6]{index=6}
    """
    url = f"{data_api_host.rstrip('/')}/positions"
    params = {"user": user_addr, "market": condition_id, "sizeThreshold": 0}
    r = requests.get(url, params=params, timeout=10)
    r.raise_for_status()
    rows = r.json() or []

    # Default empty
    up = PositionRow(outcome="Up", size=0.0, avg_price=0.0)
    down = PositionRow(outcome="Down", size=0.0, avg_price=0.0)

    for row in rows:
        o = str(row.get("outcome") or "")
        sz = float(row.get("size") or 0.0)
        ap = float(row.get("avgPrice") or 0.0)
        if o.lower() == "up":
            up = PositionRow("Up", sz, ap)
        elif o.lower() == "down":
            down = PositionRow("Down", sz, ap)

    return PositionSnapshot(up=up, down=down)


# ----------------------------
# Trading logic
# ----------------------------

@dataclass
class TopOfBook:
    up_bid: Optional[float]
    up_bid_sz: Optional[float]
    up_ask: Optional[float]
    up_ask_sz: Optional[float]
    dn_bid: Optional[float]
    dn_bid_sz: Optional[float]
    dn_ask: Optional[float]
    dn_ask_sz: Optional[float]

@dataclass
class TradeAction:
    ts: str
    action: str
    side: str
    shares: float
    unit: float
    note: str
    ok: bool
    err: str = ""
    ts_epoch: float = field(default_factory=time.time)

@dataclass
class WalletDebug:
    status: str = "unknown"
    balance: Optional[float] = None  # USDC balance when available
    matic: Optional[float] = None
    allowance: Optional[float] = None
    available: Optional[float] = None
    detail: str = ""

@dataclass
class RuntimeStats:
    up_buy_count: int
    down_buy_count: int
    up_shares: float
    down_shares: float
    up_paid: float
    down_paid: float
    up_value: float
    down_value: float
    up_pnl: float
    down_pnl: float

    @property
    def total_paid(self) -> float:
        return self.up_paid + self.down_paid

    @property
    def total_value(self) -> float:
        return self.up_value + self.down_value

    @property
    def total_pnl(self) -> float:
        return self.up_pnl + self.down_pnl

    @property
    def pnl_if_up_wins(self) -> float:
        return self.up_shares - self.total_paid

    @property
    def pnl_if_down_wins(self) -> float:
        return self.down_shares - self.total_paid

class Trader:
    def __init__(
        self,
        public_client: ClobClient,
        authed_client: Optional[ClobClient],
        meta: MarketMeta,
        *,
        poll_s: float,
        live: bool,
        max_spend_usd: float,
        min_edge: float,
        build_max: float,
        step_shares: float,
        unhedged_usd_max: float,
        data_api_host: str,
        user_addr: str,
        logger: logging.Logger,
        signature_type: int,
        funder: Optional[str],
        polygon_rpc_urls: List[str],
        min_order_shares: float,
        min_order_usd: float,
        allow_inventory_build: bool,
        settle_floor: float,
        price_feed_mode: str,
        ws_url: str,
        max_session_shares: float,
        max_trades: int,
        market_open_delay_s: int,
        disable_flip_scalp: bool,
        scalp_only_mode: bool,
        upswing_only_mode: bool,
        ml_mode: bool,
        replication_mode: bool,
        collect_mode: bool,
        hedge_only_mode: bool,
        gpt_mode: bool,
        fortress_mode: bool,
        gpt_alloc_fraction: float,
        gpt_min_signal: float,
        fortress_loss_cap: float,
        fortress_lock_edge: float,
        fortress_tilt_budget: float,
        fortress_max_imbalance: float,
        fortress_max_tilt_shares: float,
        hedge_minor_loss_limit: float,
        hedge_upside_allocation: float,
        hedge_max_extra_shares: float,
        max_side_position_shares: float,
        inventory_take_profit_cents: float,
        inventory_stop_loss_cents: float,
        sell_order_type: str,
        sell_price_mode: str,
        sell_undercut_cents: float,
        upswing_take_profit_cents: float,
        upswing_stop_loss_cents: float,
        upswing_min_momentum_cents: float,
        upswing_min_score: float,
        ml_start_cash: float,
        replication_diag_log: str,
        collect_data_csv: str,
    ):
        self.public_client = public_client
        self.authed_client = authed_client
        self.meta = meta
        self.poll_s = poll_s
        self.live = live
        self.max_spend_usd = max_spend_usd
        self.min_edge = min_edge
        self.build_max = build_max
        self.step_shares = step_shares
        self.unhedged_usd_max = unhedged_usd_max
        self.data_api_host = data_api_host
        self.user_addr = user_addr
        self.logger = logger
        self.signature_type = signature_type
        self.funder = funder
        self.polygon_rpc_urls = polygon_rpc_urls
        self.min_order_shares = max(0.1, min_order_shares)
        self.min_order_usd = max(0.1, min_order_usd)
        self.allow_inventory_build = allow_inventory_build
        self.settle_floor = settle_floor
        self.max_session_shares = max(1.0, max_session_shares)
        self.max_trades = max(0, int(max_trades))
        self.market_open_delay_s = max(0, int(market_open_delay_s))
        self.disable_flip_scalp = disable_flip_scalp
        self.scalp_only_mode = scalp_only_mode
        self.upswing_only_mode = upswing_only_mode
        self.ml_mode = ml_mode
        self.replication_mode = replication_mode
        self.collect_mode = collect_mode
        self.hedge_only_mode = hedge_only_mode
        self.gpt_mode = gpt_mode
        self.fortress_mode = fortress_mode
        self.gpt_alloc_fraction = clamp(gpt_alloc_fraction, 0.01, 1.0)
        self.gpt_min_signal = clamp(gpt_min_signal, 0.01, 1.0)
        self.fortress_loss_cap = max(0.0, fortress_loss_cap)
        self.fortress_lock_edge = max(0.0, fortress_lock_edge)
        self.fortress_tilt_budget = clamp(fortress_tilt_budget, 0.0, 1.0)
        self.fortress_max_imbalance = max(0.1, fortress_max_imbalance)
        self.fortress_max_tilt_shares = max(0.1, fortress_max_tilt_shares)
        self.hedge_minor_loss_limit = max(0.0, hedge_minor_loss_limit)
        self.hedge_upside_allocation = clamp(hedge_upside_allocation, 0.0, 1.0)
        self.hedge_max_extra_shares = max(0.1, hedge_max_extra_shares)
        self.max_side_position_shares = max(1.0, max_side_position_shares)
        self.inventory_take_profit_cents = max(0.0, inventory_take_profit_cents)
        self.inventory_stop_loss_cents = max(0.0, inventory_stop_loss_cents)
        sot = (sell_order_type or "IOC").strip().upper()
        if sot == "FAK":
            sot = "IOC"
        self.sell_order_type = sot if sot in {"IOC", "FOK", "GTC"} else "IOC"
        spm = (sell_price_mode or "bid").strip().lower()
        self.sell_price_mode = spm if spm in {"bid", "ask", "ask_minus", "bid_minus"} else "bid"
        self.sell_undercut_cents = max(0.0, sell_undercut_cents)
        self.upswing_take_profit_cents = max(0.005, upswing_take_profit_cents)
        self.upswing_stop_loss_cents = max(0.005, upswing_stop_loss_cents)
        self.upswing_min_momentum_cents = max(0.001, upswing_min_momentum_cents)
        self.upswing_min_score = max(2.0, upswing_min_score)
        self.upswing_window_s = max(12.0, parse_floatish(os.getenv("UPSWING_WINDOW_S"), 28.0))
        self.upswing_min_samples = max(8, parse_intish(os.getenv("UPSWING_MIN_SAMPLES"), 10))
        self.upswing_cooldown_s = max(0.0, parse_floatish(os.getenv("UPSWING_COOLDOWN_S"), 2.5))
        self.upswing_max_hold_s = max(6.0, parse_floatish(os.getenv("UPSWING_MAX_HOLD_S"), 35.0))
        self.upswing_trail_gap_cents = max(0.003, parse_floatish(os.getenv("UPSWING_TRAIL_GAP_CENTS"), 0.01))
        self.ml_virtual_cash = max(1.0, ml_start_cash)
        self.ml_buy_only = parse_boolish(os.getenv("ML_BUY_ONLY"), True)
        self.ml_pair_lock_edge = max(0.0, parse_floatish(os.getenv("ML_PAIR_LOCK_EDGE"), 0.01))
        self.ml_max_imbalance_shares = max(0.5, parse_floatish(os.getenv("ML_MAX_IMBALANCE_SHARES"), 8.0))
        self.ml_scores: List[float] = [0.0, 0.0, 0.0, 0.0]
        self.ml_trials: List[int] = [0, 0, 0, 0]
        self.ml_active_idx = 0
        self.ml_last_signal = "init"
        self.ml_last_switch_ts = 0.0
        self.ml_last_equity = self.ml_virtual_cash
        self.ml_up_qty = 0.0
        self.ml_dn_qty = 0.0
        self.ml_up_cost = 0.0
        self.ml_dn_cost = 0.0
        self.ml_explore_rate = clamp(parse_floatish(os.getenv("ML_EXPLORE_RATE"), 0.20), 0.0, 1.0)
        self.replication_window_s = max(15.0, parse_floatish(os.getenv("REPL_WINDOW_S"), 240.0))
        self.replication_cadence_s = max(0.5, parse_floatish(os.getenv("REPL_CADENCE_S"), 4.0))
        self.replication_min_set_edge = max(0.0, parse_floatish(os.getenv("REPL_MIN_SET_EDGE"), 0.002))
        self.replication_max_net_imbalance = max(1.0, parse_floatish(os.getenv("REPL_MAX_NET_IMBALANCE"), 150.0))
        self.replication_next_trade_ts = 0.0
        self.replication_last_set_edge = 0.0
        self.replication_diag_log = (replication_diag_log or "replication_diag.jsonl").strip()
        self._replication_diag_last_ts = 0.0
        self.collect_data_csv = (collect_data_csv or "market_collect.csv").strip()
        self.collect_samples_count = 0
        self._collect_last_ts = 0.0
        self.book_error = ""
        self.book_error_logged = False

        self.spent_est = 0.0
        self.actions: List[TradeAction] = []
        self.action_history: List[TradeAction] = []
        self.generated_html_reports: List[str] = []
        self._last_books: Optional[TopOfBook] = None
        self._last_runtime_stats: Optional[RuntimeStats] = None
        self.opps_met = 0
        self.best_profit_per_bundle = -1e9
        self.best_cost_seen = 1e9
        self.invalid_sig_hint_logged = False
        self.auth_broken = False
        self.auth_broken_notice_logged = False
        self.funds_blocked = False
        self.funds_blocked_notice_logged = False
        self.wallet_debug = WalletDebug(status="not_checked", detail="wallet balance check pending")
        self.wallet_refresh_interval_s = max(0.5, parse_floatish(os.getenv("WALLET_REFRESH_INTERVAL_S"), 20.0))
        self._wallet_debug_last_ts = 0.0
        self._last_wallet_budget_value: Optional[float] = None
        self.portfolio_start_balance: Optional[float] = None
        self.portfolio_api_value: Optional[float] = None
        self._portfolio_api_last_ts = 0.0
        self.last_positions_snapshot = PositionSnapshot(up=PositionRow("Up", 0.0, 0.0), down=PositionRow("Down", 0.0, 0.0))
        self.positions_stale = False
        self.paper_up_qty = 0.0
        self.paper_dn_qty = 0.0
        self.paper_up_cost = 0.0
        self.paper_dn_cost = 0.0
        self.paper_locked_pnl = 0.0
        self.live_locked_pnl_est = 0.0
        self.up_buy_count = 0
        self.down_buy_count = 0
        self.successful_buy_trades = 0
        self.executed_trade_count = 0
        self.up_shares_bought = 0.0
        self.down_shares_bought = 0.0
        self.up_paid_total = 0.0
        self.down_paid_total = 0.0
        self.session_bought_shares = 0.0
        self.session_bought_shares_by_market: Dict[str, float] = {self._market_session_key(): 0.0}

        # Prefer fee from meta; allow runtime override via env
        env_fee = os.getenv("TAKER_FEE_RATE")
        if env_fee:
            self.meta.taker_fee_rate = parse_floatish(env_fee, self.meta.taker_fee_rate)

        env_fee_raw = os.getenv("FEE_RATE_RAW")
        if env_fee_raw:
            self.fee_rate_raw = max(1, parse_intish(env_fee_raw, 1000))
        else:
            inferred_raw = int(round(self.meta.taker_fee_rate * 1_000_000))
            self.fee_rate_raw = max(1, inferred_raw if inferred_raw > 0 else 1000)

        env_fee_bps = os.getenv("FEE_RATE_BPS")
        if env_fee_bps:
            self.fee_rate_bps = max(1, parse_intish(env_fee_bps, self.fee_rate_raw))
        else:
            # Some py-clob-client/server paths expect the same raw fee integer in both fields.
            self.fee_rate_bps = self.fee_rate_raw

        self.fee_error_count = 0
        self.fee_broken = False
        self.last_success_trade_ts = time.time()
        self.edge_relax_after_s = max(10, parse_intish(os.getenv("EDGE_RELAX_AFTER_S"), 120))
        self.min_edge_floor = max(0.0, parse_floatish(os.getenv("MIN_EDGE_FLOOR"), 0.001))

        order_type_env = (os.getenv("ORDER_TYPE") or "FOK").strip().upper()
        self.order_type = order_type_env if order_type_env in {"FOK", "IOC", "GTC"} else "FOK"
        require_fill_env = (os.getenv("REQUIRE_IMMEDIATE_FILL") or "1").strip().lower()
        self.require_immediate_fill = require_fill_env not in {"0", "false", "no", "off"}
        self.price_feed_mode = (price_feed_mode or "poll").strip().lower()
        self.ws_url = ws_url
        self.ws_book: Optional[TopOfBook] = None
        self.ws_last_update_ts = 0.0
        self.ws_failure_detail = ""
        self.ws_started = False
        self.pending_fill_checks: List[Dict[str, Any]] = []
        self.pending_pair_unwinds: Dict[str, Dict[str, Any]] = {}
        self.pending_unwind_sell_checks: List[Dict[str, Any]] = []
        self.pending_risk_sell_checks: List[Dict[str, Any]] = []
        self.risk_sell_side_hold_until: Dict[str, float] = {"UP": 0.0, "DOWN": 0.0}
        self.risk_sell_settle_gate: Dict[str, Dict[str, float]] = {"UP": {"until": 0.0, "target": 0.0}, "DOWN": {"until": 0.0, "target": 0.0}}
        self.risk_sell_next_retry_ts: Dict[str, float] = {"UP": 0.0, "DOWN": 0.0}
        self.risk_sell_confirm_wait_until: Dict[str, float] = {"UP": 0.0, "DOWN": 0.0}
        self.post_risk_rebalance_cooldown_until_ts = 0.0
        self.require_rebuild_after_risk_sell = False
        self.pair_fill_grace_until_ts = 0.0
        self.next_pending_recheck_ts = 0.0
        self.pending_recheck_interval_s = 2.0
        self.max_net_imbalance_shares = max(0.5, parse_floatish(os.getenv("MAX_NET_IMBALANCE_SHARES"), 1.0))
        self.rebalance_only_mode = False
        self.skip_reasons: Dict[str, int] = {}
        self.api_metrics: Dict[str, Dict[str, float]] = {}
        self.flip_open: Dict[str, Dict[str, float]] = {}
        self.upswing_open: Dict[str, Dict[str, float]] = {}
        self.upswing_signal_debug: Dict[str, str] = {"UP": "init", "DOWN": "init"}
        self.upswing_last_exit_ts: Dict[str, float] = {"UP": 0.0, "DOWN": 0.0}
        self.flip_history: Dict[str, deque] = {"UP": deque(maxlen=96), "DOWN": deque(maxlen=96)}
        self.flip_stop_loss_cents = max(0.01, parse_floatish(os.getenv("FLIP_STOP_LOSS_CENTS"), 0.02))
        self.flip_target_cents = max(0.005, parse_floatish(os.getenv("FLIP_TARGET_CENTS"), 0.01))
        self.flip_signal_window_s = max(12, parse_intish(os.getenv("FLIP_SIGNAL_WINDOW_S"), 35))
        self.flip_min_samples = max(8, parse_intish(os.getenv("FLIP_MIN_SAMPLES"), 12))
        self.flip_cooldown_s = max(0.0, parse_floatish(os.getenv("FLIP_COOLDOWN_S"), 3.0))
        self.flip_max_spread = max(0.002, parse_floatish(os.getenv("FLIP_MAX_SPREAD"), 0.012))
        self.flip_min_expected_edge = max(0.0, parse_floatish(os.getenv("FLIP_MIN_EXPECTED_EDGE"), 0.002))
        self.flip_entry_price_min = clamp(parse_floatish(os.getenv("FLIP_ENTRY_PRICE_MIN"), 0.20), 0.01, 0.95)
        self.flip_entry_price_max = clamp(parse_floatish(os.getenv("FLIP_ENTRY_PRICE_MAX"), 0.75), 0.05, 0.99)
        self.flip_max_window_drift = max(0.005, parse_floatish(os.getenv("FLIP_MAX_WINDOW_DRIFT"), 0.035))
        self.flip_min_rebound_cents = max(0.002, parse_floatish(os.getenv("FLIP_MIN_REBOUND_CENTS"), 0.008))
        self.flip_max_hold_s = max(5.0, parse_floatish(os.getenv("FLIP_MAX_HOLD_S"), 45.0))
        self.flip_trail_arm_cents = max(0.002, parse_floatish(os.getenv("FLIP_TRAIL_ARM_CENTS"), 0.006))
        self.flip_trail_gap_cents = max(0.001, parse_floatish(os.getenv("FLIP_TRAIL_GAP_CENTS"), 0.004))
        self.flip_stoploss_streak_limit = max(1, parse_intish(os.getenv("FLIP_STOPLOSS_STREAK_LIMIT"), 3))
        self.flip_pause_after_stops_s = max(5.0, parse_floatish(os.getenv("FLIP_PAUSE_AFTER_STOPS_S"), 60.0))
        self.flip_hold_hedged_pairs = (os.getenv("FLIP_HOLD_HEDGED_PAIRS", "1").strip().lower() not in {"0", "false", "no", "off"})
        self.flip_hold_min_edge = max(0.0, parse_floatish(os.getenv("FLIP_HOLD_MIN_EDGE"), 0.01))
        self.flip_pause_until_ts = 0.0
        self.flip_stoploss_streak = 0
        self.flip_last_exit_ts: Dict[str, float] = {"UP": 0.0, "DOWN": 0.0}
        self.flip_next_exit_retry_ts: Dict[str, float] = {"UP": 0.0, "DOWN": 0.0}
        self.flip_exit_fail_count: Dict[str, int] = {"UP": 0, "DOWN": 0}
        self.flip_signal_debug: Dict[str, str] = {"UP": "init", "DOWN": "init"}
        self.flip_hedge_reserve_qty = max(0.0, parse_floatish(os.getenv("FLIP_HEDGE_RESERVE_QTY"), 0.0))
        self.btc_spot_history: deque = deque(maxlen=240)
        self._last_btc_fetch_ts = 0.0
        self._last_btc_server_ts = 0.0
        self._last_btc_price: Optional[float] = None
        self.gpt_last_signal = "n/a"
        self.btc_price_source = "n/a"
        self.chainlink_decimals: Optional[int] = None
        self.chainlink_last_updated_at: Optional[int] = None
        self.chainlink_stale_after_s = max(0.5, parse_floatish(os.getenv("BTC_CHAINLINK_STALE_AFTER_S"), 2.0))
        self.btc_low_latency_mode = parse_boolish(os.getenv("BTC_LOW_LATENCY_MODE"), True)
        self.btc_fast_probe_timeout_s = max(0.15, parse_floatish(os.getenv("BTC_FAST_PROBE_TIMEOUT_S"), 0.45))
        self.btc_ws_enabled = parse_boolish(os.getenv("BTC_WS_ENABLED"), True)
        self.btc_ws_url = os.getenv("BTC_WS_URL", "wss://stream.binance.com:9443/ws/btcusdt@trade")
        self.btc_prefer_ws = parse_boolish(os.getenv("BTC_PREFER_WS"), True)
        self.btc_ws_started = False
        self.btc_ws_last_update_ts = 0.0
        self.btc_ws_failure_detail = ""
        self.btc_market_open_price: Optional[float] = None
        self.btc_market_open_source = "pending"
        self.btc_market_open_anchor_ts = int(self.meta.start_dt_utc.timestamp()) if self.meta.start_dt_utc else None
        self.btc_fetch_min_interval_s = max(0.02, parse_floatish(os.getenv("BTC_FETCH_MIN_INTERVAL_S"), 0.2))
        if self.collect_mode:
            self.btc_fetch_min_interval_s = min(self.btc_fetch_min_interval_s, 0.05)

    def _ensure_runtime_guards(self) -> None:
        """Backfill newer runtime guard attrs for older live objects/configs."""
        if not isinstance(getattr(self, "risk_sell_side_hold_until", None), dict):
            self.risk_sell_side_hold_until = {"UP": 0.0, "DOWN": 0.0}
        if not isinstance(getattr(self, "risk_sell_settle_gate", None), dict):
            self.risk_sell_settle_gate = {"UP": {"until": 0.0, "target": 0.0}, "DOWN": {"until": 0.0, "target": 0.0}}
        if not isinstance(getattr(self, "risk_sell_next_retry_ts", None), dict):
            self.risk_sell_next_retry_ts = {"UP": 0.0, "DOWN": 0.0}
        if not isinstance(getattr(self, "risk_sell_confirm_wait_until", None), dict):
            self.risk_sell_confirm_wait_until = {"UP": 0.0, "DOWN": 0.0}
        if not hasattr(self, "post_risk_rebalance_cooldown_until_ts"):
            self.post_risk_rebalance_cooldown_until_ts = 0.0
        if not hasattr(self, "require_rebuild_after_risk_sell"):
            self.require_rebuild_after_risk_sell = False

    def remaining_budget(self) -> float:
        return max(0.0, self.max_spend_usd - self.spent_est)

    def _record_skip(self, reason: str):
        self.skip_reasons[reason] = self.skip_reasons.get(reason, 0) + 1

    def _extract_status_code(self, err: Any) -> Optional[int]:
        s = str(err or "")
        m = re.search(r"status_code=(\d+)", s)
        if m:
            return int(m.group(1))
        m = re.search(r"\b(\d{3})\b", s)
        if m and m.group(1) in {"400", "401", "403", "404", "408", "409", "422", "429", "500", "502", "503", "504"}:
            return int(m.group(1))
        return None

    def _record_api_metric(self, endpoint: str, latency_s: float, ok: bool, status_code: Optional[int] = None):
        stat = self.api_metrics.setdefault(endpoint, {
            "ok": 0.0,
            "fail": 0.0,
            "http_429": 0.0,
            "latency_total_ms": 0.0,
            "latency_count": 0.0,
        })
        stat["ok" if ok else "fail"] += 1.0
        stat["latency_total_ms"] += max(0.0, latency_s) * 1000.0
        stat["latency_count"] += 1.0
        if status_code == 429:
            stat["http_429"] += 1.0

    def _format_api_metric(self, endpoint: str) -> str:
        s = self.api_metrics.get(endpoint)
        if not s:
            return f"{endpoint}:n/a"
        cnt = max(1.0, s.get("latency_count", 0.0))
        avg = s.get("latency_total_ms", 0.0) / cnt
        return (
            f"{endpoint}:ok={int(s.get('ok', 0.0))} fail={int(s.get('fail', 0.0))} "
            f"429={int(s.get('http_429', 0.0))} avg_ms={avg:.1f}"
        )

    def time_to_end_s(self) -> Optional[int]:
        if not self.meta.end_dt_utc:
            return None
        return int((self.meta.end_dt_utc - now_utc()).total_seconds())

    def market_open_wait_remaining_s(self) -> Optional[int]:
        if (not self.meta.start_dt_utc) or self.market_open_delay_s <= 0:
            return None
        unlock_ts = self.meta.start_dt_utc.timestamp() + float(self.market_open_delay_s)
        return max(0, int(math.ceil(unlock_ts - time.time())))

    def _ws_parse_top(self, payload: Any, token_id: str) -> Optional[Tuple[Optional[float], Optional[float], Optional[float], Optional[float]]]:
        if not isinstance(payload, dict):
            return None
        asset = str(payload.get("asset_id") or payload.get("token_id") or payload.get("market") or "")
        if asset and asset != token_id:
            return None
        bids = payload.get("bids")
        asks = payload.get("asks")
        if bids is None and asks is None:
            return None
        return best_from_book({"bids": bids or [], "asks": asks or []})

    def _ws_ingest_message(self, msg: str):
        try:
            obj = json.loads(msg)
        except Exception:
            return
        items = obj if isinstance(obj, list) else [obj]
        up = None
        dn = None
        for it in items:
            pu = self._ws_parse_top(it, self.meta.token_ids[0])
            pd = self._ws_parse_top(it, self.meta.token_ids[1])
            if pu:
                up = pu
            if pd:
                dn = pd
        if up or dn:
            cur = self.ws_book or TopOfBook(None, None, None, None, None, None, None, None)
            self.ws_book = TopOfBook(
                up_bid=(up[0] if up else cur.up_bid),
                up_bid_sz=(up[1] if up else cur.up_bid_sz),
                up_ask=(up[2] if up else cur.up_ask),
                up_ask_sz=(up[3] if up else cur.up_ask_sz),
                dn_bid=(dn[0] if dn else cur.dn_bid),
                dn_bid_sz=(dn[1] if dn else cur.dn_bid_sz),
                dn_ask=(dn[2] if dn else cur.dn_ask),
                dn_ask_sz=(dn[3] if dn else cur.dn_ask_sz),
            )
            self.ws_last_update_ts = time.time()

    def _start_ws_price_feed(self):
        if self.ws_started or self.price_feed_mode != "ws":
            return
        self.ws_started = True

        up_token, dn_token = self.meta.token_ids[0], self.meta.token_ids[1]
        def _worker():
            while True:
                try:
                    def on_open(ws):
                        sub_msgs = [
                            {"type": "market", "assets_ids": [up_token, dn_token]},
                            {"type": "market", "asset_ids": [up_token, dn_token]},
                            {"event": "subscribe", "assets_ids": [up_token, dn_token]},
                        ]
                        for m in sub_msgs:
                            try:
                                ws.send(json.dumps(m))
                            except Exception:
                                pass
                    def on_message(_ws, message):
                        self._ws_ingest_message(message)
                    def on_error(_ws, err):
                        self.ws_failure_detail = str(err)
                    def on_close(_ws, *_args):
                        pass
                    app = websocket.WebSocketApp(self.ws_url, on_open=on_open, on_message=on_message, on_error=on_error, on_close=on_close)
                    app.run_forever(ping_interval=20, ping_timeout=10)
                except Exception as e:
                    self.ws_failure_detail = repr(e)
                time.sleep(1.0)

        threading.Thread(target=_worker, daemon=True).start()

    def fetch_books(self) -> TopOfBook:
        up_token, dn_token = self.meta.token_ids[0], self.meta.token_ids[1]

        if self.price_feed_mode == "ws":
            self._start_ws_price_feed()
            if self.ws_book and (time.time() - self.ws_last_update_ts) <= 3.0:
                return self.ws_book

        t0 = time.time()
        try:
            up_book = self.public_client.get_order_book(up_token)
            dn_book = self.public_client.get_order_book(dn_token)
        except Exception as e:
            self._record_api_metric("clob.orderbook", time.time() - t0, ok=False, status_code=self._extract_status_code(e))
            msg = str(e)
            self.book_error = msg
            if ("No orderbook exists" in msg or "status_code=404" in msg) and not self.book_error_logged:
                self.book_error_logged = True
                self.logger.error(
                    "No orderbook exists for discovered token ids (up=%s down=%s). Pick an active slug from the menu.",
                    up_token,
                    dn_token,
                )
            return TopOfBook(None, None, None, None, None, None, None, None)

        self._record_api_metric("clob.orderbook", time.time() - t0, ok=True)

        self.book_error = ""
        self.book_error_logged = False
        up_bid, up_bid_sz, up_ask, up_ask_sz = best_from_book(up_book)
        dn_bid, dn_bid_sz, dn_ask, dn_ask_sz = best_from_book(dn_book)

        return TopOfBook(
            up_bid=up_bid, up_bid_sz=up_bid_sz, up_ask=up_ask, up_ask_sz=up_ask_sz,
            dn_bid=dn_bid, dn_bid_sz=dn_bid_sz, dn_ask=dn_ask, dn_ask_sz=dn_ask_sz,
        )

    def positions(self) -> PositionSnapshot:
        t0 = time.time()
        try:
            snap = fetch_positions(self.data_api_host, self.user_addr, self.meta.condition_id, self.logger)
            self._record_api_metric("data_api.positions", time.time() - t0, ok=True)
            self.last_positions_snapshot = snap
            self.positions_stale = False
            return snap
        except Exception as e:
            self._record_api_metric("data_api.positions", time.time() - t0, ok=False, status_code=self._extract_status_code(e))
            self.logger.exception("positions_fetch_failed")
            self.positions_stale = True
            # Critical safety: keep last known positions instead of zeroing out inventory,
            # otherwise the bot can over-buy due to temporary data-api failures.
            return self.last_positions_snapshot

    def est_effective_cost(self, notional: float) -> float:
        # taker fee is applied to trade notional (approx). :contentReference[oaicite:7]{index=7}
        return notional * (1.0 + self.meta.taker_fee_rate)

    def log_action(self, a: TradeAction):
        self.actions = (self.actions + [a])[-10:]
        self.action_history.append(a)
        if a.ok:
            self.executed_trade_count += 1
        if a.ok and a.action.upper() == "BUY":
            self.last_success_trade_ts = time.time()
        if a.ok:
            self.logger.info("ACTION ok=%s %s %s shares=%.4f unit=%.4f note=%s", a.ok, a.action, a.side, a.shares, a.unit, a.note)
        else:
            self.logger.warning("ACTION ok=%s %s %s shares=%.4f unit=%.4f note=%s err=%s", a.ok, a.action, a.side, a.shares, a.unit, a.note, a.err)

    def _reconcile_recent_actions_from_position_delta(self, prev_pos: PositionSnapshot, cur_pos: PositionSnapshot):
        """Mark recent uncertain failed actions as confirmed when position delta proves fill happened."""
        now_ts = time.time()
        deltas = {
            "UP": max(0.0, cur_pos.up.size - prev_pos.up.size),
            "DOWN": max(0.0, cur_pos.down.size - prev_pos.down.size),
        }
        sell_deltas = {
            "UP": max(0.0, prev_pos.up.size - cur_pos.up.size),
            "DOWN": max(0.0, prev_pos.down.size - cur_pos.down.size),
        }

        def _is_uncertain_err(msg: str) -> bool:
            m = (msg or "").lower()
            return (
                "order_not_filled_immediately" in m
                or "request exception" in m
                or "status_code=none" in m
                or "not enough balance" in m
                or "allowance" in m
            )

        for action in reversed(self.action_history):
            if action.ok:
                continue
            if (now_ts - float(action.ts_epoch or now_ts)) > 90:
                break
            side = (action.side or "").upper()
            if side not in {"UP", "DOWN"}:
                continue
            if action.action.upper() == "BUY" and deltas[side] >= max(0.1, action.shares * 0.5) and _is_uncertain_err(action.err):
                action.ok = True
                action.err = ""
                action.note = f"{action.note} | confirmed filled via position delta"
                self.executed_trade_count += 1
                self.last_success_trade_ts = time.time()
                deltas[side] = max(0.0, deltas[side] - action.shares)
                self.logger.info("Action reconciled as filled from position delta; action=BUY side=%s shares=%.4f", side, action.shares)
            elif action.action.upper() == "SELL" and sell_deltas[side] >= max(0.1, action.shares * 0.5) and _is_uncertain_err(action.err):
                action.ok = True
                action.err = ""
                action.note = f"{action.note} | confirmed filled via position delta"
                self.executed_trade_count += 1
                sell_deltas[side] = max(0.0, sell_deltas[side] - action.shares)
                if "risk rebalance sell" in (action.note or "").lower():
                    self.require_rebuild_after_risk_sell = True
                    self.risk_sell_confirm_wait_until[side] = max(self.risk_sell_confirm_wait_until.get(side, 0.0), time.time() + 12.0)
                self.logger.info("Action reconciled as filled from position delta; action=SELL side=%s shares=%.4f", side, action.shares)

    def export_trade_csv(self, out_dir: str, tz_name: str = "America/Toronto") -> Optional[str]:
        try:
            export_dir = Path(out_dir)
            export_dir.mkdir(parents=True, exist_ok=True)
            safe_slug = re.sub(r"[^a-zA-Z0-9_-]+", "-", self.meta.slug)
            stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
            path = export_dir / f"trades_{safe_slug}_{stamp}.csv"
            tz = ZoneInfo(tz_name)

            headers = [
                "row",
                "market_slug",
                "market_question",
                "condition_id",
                "market_start_utc",
                "market_end_utc",
                "action_ts_utc",
                "action_ts_toronto",
                "action",
                "side",
                "shares",
                "unit_price",
                "notional_usd",
                "est_fee_usd",
                "est_cash_impact_usd",
                "ok",
                "note",
                "error",
                "spent_est_after_action",
                "session_bought_shares",
                "max_session_shares",
                "executed_trade_count",
                "max_trades",
                "price_feed_mode",
                "ws_last_update_ts",
            ]

            with path.open("w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(headers)
                for i, a in enumerate(self.action_history, start=1):
                    dt_utc = datetime.fromtimestamp(a.ts_epoch, tz=timezone.utc)
                    dt_tor = dt_utc.astimezone(tz)
                    notional = float(a.shares) * float(a.unit)
                    fee = notional * self.meta.taker_fee_rate
                    cash_impact = (notional + fee) if a.action.upper() == "BUY" else -(max(0.0, notional - fee))
                    w.writerow([
                        i,
                        self.meta.slug,
                        self.meta.question,
                        self.meta.condition_id,
                        "" if not self.meta.start_dt_utc else self.meta.start_dt_utc.isoformat(),
                        "" if not self.meta.end_dt_utc else self.meta.end_dt_utc.isoformat(),
                        dt_utc.isoformat(),
                        dt_tor.isoformat(),
                        a.action,
                        a.side,
                        f"{a.shares:.8f}",
                        f"{a.unit:.8f}",
                        f"{notional:.8f}",
                        f"{fee:.8f}",
                        f"{cash_impact:.8f}",
                        a.ok,
                        a.note,
                        a.err,
                        f"{self.spent_est:.8f}",
                        f"{self.session_bought_shares:.8f}",
                        f"{self.max_session_shares:.8f}",
                        self.executed_trade_count,
                        self.max_trades,
                        self.price_feed_mode,
                        f"{self.ws_last_update_ts:.6f}",
                    ])
            self.logger.info("Wrote market trade CSV: %s rows=%s tz=%s", str(path), len(self.action_history), tz_name)
            return str(path)
        except Exception:
            self.logger.exception("trade_csv_export_failed")
            return None

    def export_trade_html(self, out_dir: str, tz_name: str = "America/Toronto") -> Optional[str]:
        try:
            export_dir = Path(out_dir)
            export_dir.mkdir(parents=True, exist_ok=True)
            safe_slug = re.sub(r"[^a-zA-Z0-9_-]+", "-", self.meta.slug)
            safe_q = re.sub(r"[^a-zA-Z0-9_-]+", "-", (self.meta.question or "market").strip()).strip("-")[:72] or "market"
            stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
            path = export_dir / f"trades_{safe_slug}_{safe_q}_{stamp}.html"
            tz = ZoneInfo(tz_name)

            start_budget = float(self.max_spend_usd)
            spent_now = float(self.spent_est)
            runtime = self._last_runtime_stats
            books = self._last_books

            ml_equity = start_budget
            if books is not None:
                ml_equity = self._ml_equity_mark(books)

            end_value = ml_equity if self.ml_mode else (runtime.total_value if runtime else 0.0)
            pnl = (ml_equity - start_budget) if self.ml_mode else ((runtime.total_pnl if runtime else 0.0))
            pnl_pct = (pnl / start_budget * 100.0) if start_budget > 0 else 0.0

            held_up_qty = self.ml_up_qty if self.ml_mode else self.paper_up_qty
            held_dn_qty = self.ml_dn_qty if self.ml_mode else self.paper_dn_qty
            held_up_avg = (self.ml_up_cost / max(1e-9, self.ml_up_qty)) if self.ml_mode and self.ml_up_qty > 0 else ((self.paper_up_cost / max(1e-9, self.paper_up_qty)) if ((not self.ml_mode) and self.paper_up_qty > 0) else 0.0)
            held_dn_avg = (self.ml_dn_cost / max(1e-9, self.ml_dn_qty)) if self.ml_mode and self.ml_dn_qty > 0 else ((self.paper_dn_cost / max(1e-9, self.paper_dn_qty)) if ((not self.ml_mode) and self.paper_dn_qty > 0) else 0.0)

            action_ok = sum(1 for a in self.action_history if a.ok)
            action_fail = len(self.action_history) - action_ok
            buy_ok = sum(1 for a in self.action_history if a.ok and a.action.upper() == "BUY")
            sell_ok = sum(1 for a in self.action_history if a.ok and a.action.upper() == "SELL")

            book_summary = "n/a"
            if books is not None:
                book_summary = (
                    f"UP bid/ask={('-' if books.up_bid is None else f'{books.up_bid:.4f}')}/"
                    f"{('-' if books.up_ask is None else f'{books.up_ask:.4f}')} | "
                    f"DOWN bid/ask={('-' if books.dn_bid is None else f'{books.dn_bid:.4f}')}/"
                    f"{('-' if books.dn_ask is None else f'{books.dn_ask:.4f}')}"
                )

            runtime_rows = ""
            if runtime is not None:
                runtime_rows = f"""
<tr><th>UP buys / shares</th><td>{runtime.up_buy_count} / {runtime.up_shares:.4f}</td></tr>
<tr><th>DOWN buys / shares</th><td>{runtime.down_buy_count} / {runtime.down_shares:.4f}</td></tr>
<tr><th>Total paid / value / PnL</th><td>{runtime.total_paid:.4f} / {runtime.total_value:.4f} / {runtime.total_pnl:+.4f}</td></tr>
<tr><th>PnL if UP settles @ $1</th><td>{runtime.pnl_if_up_wins:+.4f}</td></tr>
<tr><th>PnL if DOWN settles @ $1</th><td>{runtime.pnl_if_down_wins:+.4f}</td></tr>
"""

            rows = []
            for i, a in enumerate(self.action_history, start=1):
                dt_utc = datetime.fromtimestamp(a.ts_epoch, tz=timezone.utc)
                dt_tor = dt_utc.astimezone(tz)
                notional = float(a.shares) * float(a.unit)
                fee = notional * self.meta.taker_fee_rate
                rows.append(
                    f"<tr><td>{i}</td><td>{escape(dt_tor.strftime('%Y-%m-%d %H:%M:%S %Z'))}</td><td>{escape(a.action)}</td><td>{escape(a.side)}</td><td>{a.shares:.4f}</td><td>{a.unit:.4f}</td><td>{notional:.4f}</td><td>{fee:.4f}</td><td>{escape(a.note)}</td><td>{'OK' if a.ok else 'FAIL'}</td><td>{escape(a.err)}</td></tr>"
                )

            html = f"""<!doctype html>
<html><head><meta charset='utf-8'><title>Trade Report {escape(self.meta.slug)}</title>
<style>
body{{font-family:Inter,Segoe UI,Arial,sans-serif;background:#0b1020;color:#e7ecff;padding:20px;line-height:1.35}}
.card{{background:#111831;border:1px solid #2a365e;border-radius:12px;padding:14px;margin-bottom:14px;box-shadow:0 1px 8px rgba(0,0,0,.25)}}
.grid{{display:grid;grid-template-columns:1fr 1fr;gap:14px}}
.small{{font-size:12px;color:#b6c2ef}}
h1,h2,h3{{margin:0 0 10px 0}} h1{{font-size:24px}} h2{{font-size:18px}} h3{{font-size:15px}}
table{{width:100%;border-collapse:collapse;font-size:13px}}th,td{{border:1px solid #2a365e;padding:7px;text-align:left;vertical-align:top}}
th{{background:#1a2448}}
.good{{color:#31d17c;font-weight:700}} .bad{{color:#ff6b6b;font-weight:700}}
.mono{{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}}
</style></head><body>
<h1>Polymarket Market Report</h1>
<div class='small'>Generated (Toronto): {escape(datetime.now(tz).strftime('%Y-%m-%d %H:%M:%S %Z'))}</div>
<div class='card'>
<h2>{escape(self.meta.question)}</h2>
<div class='mono'>slug={escape(self.meta.slug)} | condition={escape(self.meta.condition_id)}</div>
<div class='small'>Mode: {'ML buy-only (paper)' if self.ml_mode else ('LIVE' if self.live else 'PAPER')} | Feed: {escape(self.price_feed_mode)} | WS last update ts: {self.ws_last_update_ts:.3f}</div>
</div>
<div class='grid'>
<div class='card'>
<h3>Financial summary</h3>
<table>
<tr><th>Max spend</th><td>{start_budget:.4f}</td></tr>
<tr><th>Spent</th><td>{spent_now:.4f}</td></tr>
<tr><th>End marked value</th><td>{end_value:.4f}</td></tr>
<tr><th>End result (PnL)</th><td class='{('good' if pnl >= 0 else 'bad')}'>{pnl:+.4f} ({pnl_pct:+.2f}%)</td></tr>
<tr><th>Held UP @ avg</th><td>{held_up_qty:.4f} @ {held_up_avg:.4f}</td></tr>
<tr><th>Held DOWN @ avg</th><td>{held_dn_qty:.4f} @ {held_dn_avg:.4f}</td></tr>
<tr><th>Action counts</th><td>total={len(self.action_history)} ok={action_ok} fail={action_fail} buy_ok={buy_ok} sell_ok={sell_ok}</td></tr>
</table>
</div>
<div class='card'>
<h3>Market/runtime details</h3>
<table>
<tr><th>Question</th><td>{escape(self.meta.question)}</td></tr>
<tr><th>Outcomes</th><td>{escape(', '.join(self.meta.outcomes))}</td></tr>
<tr><th>Interval (s)</th><td>{self.meta.interval_s}</td></tr>
<tr><th>Start UTC</th><td>{'' if not self.meta.start_dt_utc else escape(self.meta.start_dt_utc.isoformat())}</td></tr>
<tr><th>End UTC</th><td>{'' if not self.meta.end_dt_utc else escape(self.meta.end_dt_utc.isoformat())}</td></tr>
<tr><th>Top of book snapshot</th><td class='mono'>{escape(book_summary)}</td></tr>
{runtime_rows}
</table>
</div>
</div>
<div class='card'>
<h3>Action log ({len(self.action_history)} rows)</h3>
<table><thead><tr><th>#</th><th>Time (Toronto)</th><th>Action</th><th>Side</th><th>Shares</th><th>Unit</th><th>Notional</th><th>Est fee</th><th>Note</th><th>Status</th><th>Error</th></tr></thead>
<tbody>{''.join(rows)}</tbody></table>
</div>
</body></html>"""
            path.write_text(html, encoding='utf-8')
            self.generated_html_reports = (self.generated_html_reports + [str(path)])[-8:]
            self.logger.info("Wrote market trade HTML: %s rows=%s tz=%s", str(path), len(self.action_history), tz_name)
            return str(path)
        except Exception:
            self.logger.exception("trade_html_export_failed")
            return None

    def effective_min_edge(self) -> float:
        idle_s = max(0.0, time.time() - self.last_success_trade_ts)
        if idle_s <= self.edge_relax_after_s:
            return self.min_edge
        # Gradually relax toward a configurable floor if no fills are happening.
        relax_window = max(30.0, float(self.edge_relax_after_s) * 4.0)
        frac = min(1.0, (idle_s - self.edge_relax_after_s) / relax_window)
        return self.min_edge - ((self.min_edge - self.min_edge_floor) * frac)

    def _record_paper_fill(self, token_id: str, price: float, size: float):
        if token_id == self.meta.token_ids[0]:
            self.paper_up_qty += size
            self.paper_up_cost += self.est_effective_cost(price * size)
        elif token_id == self.meta.token_ids[1]:
            self.paper_dn_qty += size
            self.paper_dn_cost += self.est_effective_cost(price * size)

        hedged = min(self.paper_up_qty, self.paper_dn_qty)
        if hedged <= 0:
            self.paper_locked_pnl = 0.0
            return

        avg_up = (self.paper_up_cost / self.paper_up_qty) if self.paper_up_qty > 0 else 0.0
        avg_dn = (self.paper_dn_cost / self.paper_dn_qty) if self.paper_dn_qty > 0 else 0.0
        self.paper_locked_pnl = hedged * (1.0 - (avg_up + avg_dn))

    def _paper_position_snapshot(self) -> PositionSnapshot:
        up_avg = (self.paper_up_cost / self.paper_up_qty) if self.paper_up_qty > 0 else 0.0
        dn_avg = (self.paper_dn_cost / self.paper_dn_qty) if self.paper_dn_qty > 0 else 0.0
        return PositionSnapshot(
            up=PositionRow("Up", self.paper_up_qty, up_avg),
            down=PositionRow("Down", self.paper_dn_qty, dn_avg),
        )

    def _market_session_key(self) -> str:
        return (self.meta.condition_id or self.meta.slug or "unknown_market").strip().lower()

    def _current_market_session_bought_shares(self) -> float:
        key = self._market_session_key()
        return max(0.0, float(self.session_bought_shares_by_market.get(key, 0.0)))

    def _record_purchase(self, token_id: str, price: float, size: float):
        paid = self.est_effective_cost(price * size)
        key = self._market_session_key()
        self.session_bought_shares_by_market[key] = self._current_market_session_bought_shares() + size
        self.session_bought_shares = self._current_market_session_bought_shares()
        self.successful_buy_trades += 1
        if token_id == self.meta.token_ids[0]:
            self.up_buy_count += 1
            self.up_shares_bought += size
            self.up_paid_total += paid
        elif token_id == self.meta.token_ids[1]:
            self.down_buy_count += 1
            self.down_shares_bought += size
            self.down_paid_total += paid

    def remaining_session_shares(self) -> float:
        return max(0.0, self.max_session_shares - self._current_market_session_bought_shares())

    def remaining_buy_trades(self) -> Optional[int]:
        if self.max_trades <= 0:
            return None
        return max(0, self.max_trades - self.executed_trade_count)

    def _can_open_new_buy(self) -> bool:
        rem = self.remaining_buy_trades()
        if rem is None:
            return True
        # Reserve one slot per currently-open flip position so exits remain possible.
        reserved_for_exits = len(self.flip_open) + len(self.upswing_open)
        return rem > (reserved_for_exits + 1)

    def _limit_buy_qty_by_session(self, qty: float) -> float:
        return max(0.0, min(qty, self.remaining_session_shares()))

    def compute_runtime_stats(self, books: TopOfBook) -> RuntimeStats:
        up_val = self.up_shares_bought * (books.up_bid or 0.0)
        dn_val = self.down_shares_bought * (books.dn_bid or 0.0)
        return RuntimeStats(
            up_buy_count=self.up_buy_count,
            down_buy_count=self.down_buy_count,
            up_shares=self.up_shares_bought,
            down_shares=self.down_shares_bought,
            up_paid=self.up_paid_total,
            down_paid=self.down_paid_total,
            up_value=up_val,
            down_value=dn_val,
            up_pnl=up_val - self.up_paid_total,
            down_pnl=dn_val - self.down_paid_total,
        )

    def _risk_guard_snapshot(self, pos: PositionSnapshot) -> PositionSnapshot:
        """Use local successful-buy accounting as a floor while external positions API catches up."""
        if (not self.live) or self.ml_mode:
            return pos

        up_size = max(max(0.0, pos.up.size), max(0.0, self.up_shares_bought))
        dn_size = max(max(0.0, pos.down.size), max(0.0, self.down_shares_bought))

        up_avg_local = (self.up_paid_total / self.up_shares_bought) if self.up_shares_bought > 0 else 0.0
        dn_avg_local = (self.down_paid_total / self.down_shares_bought) if self.down_shares_bought > 0 else 0.0

        up_avg = pos.up.avg_price
        dn_avg = pos.down.avg_price
        if up_size > max(0.0, pos.up.size):
            up_avg = up_avg_local
        if dn_size > max(0.0, pos.down.size):
            dn_avg = dn_avg_local

        return PositionSnapshot(
            up=PositionRow("Up", up_size, up_avg),
            down=PositionRow("Down", dn_size, dn_avg),
        )

    def _sync_accounting_from_positions(self, pos: PositionSnapshot):
        """Conservative accounting sync so budget/risk never understates existing holdings."""
        up_sz = max(0.0, pos.up.size)
        dn_sz = max(0.0, pos.down.size)
        up_paid_est = self.est_effective_cost(max(0.0, pos.up.avg_price) * up_sz)
        dn_paid_est = self.est_effective_cost(max(0.0, pos.down.avg_price) * dn_sz)

        # Never let tracked position accounting fall below real held inventory.
        self.up_shares_bought = max(self.up_shares_bought, up_sz)
        self.down_shares_bought = max(self.down_shares_bought, dn_sz)
        self.up_paid_total = max(self.up_paid_total, up_paid_est)
        self.down_paid_total = max(self.down_paid_total, dn_paid_est)

        inventory_cost_floor = up_paid_est + dn_paid_est
        if self.spent_est < inventory_cost_floor:
            self.spent_est = inventory_cost_floor

    def _order_args(self, token_id: str, price: float, size: float, side: str = BUY_SIDE) -> Any:
        """Build order args in a way compatible with multiple py-clob-client versions."""
        payload = {
            "token_id": token_id,
            "price": float(price),
            "size": float(size),
            "side": side,
            "fee_rate_bps": int(self.fee_rate_bps),
            "fee_rate": int(self.fee_rate_raw),
        }
        if OrderArgs is not None:
            try:
                base = OrderArgs(token_id=payload["token_id"], price=payload["price"], size=payload["size"], side=payload["side"])
                # Best-effort: attach fee attrs for client versions that read them from order args.
                try:
                    setattr(base, "fee_rate_bps", payload["fee_rate_bps"])
                    setattr(base, "fee_rate", payload["fee_rate"])
                except Exception:
                    pass
                return base
            except Exception:
                # Some versions have differing constructor signatures.
                pass
        # create_and_post_order() ultimately needs attribute access (e.g., .token_id)
        return SimpleNamespace(**payload)

    def _post_sell(self, token_id: str, price: float, size: float, note: str) -> Tuple[bool, str]:
        if not self.live:
            self._record_paper_sale(token_id, size)
            return True, ""
        if not self.authed_client:
            return False, "No authed client"
        if self.auth_broken or self.funds_blocked or self.fee_broken:
            return False, "Trading paused; sell unavailable"
        t0 = time.time()
        try:
            order = self.authed_client.create_and_post_order(
                self._order_args(token_id, price, size, side=SELL_SIDE),
                self._order_options(for_sell=True),
            )
            ok_fill, fill_err = self._order_looks_filled(order)
            self._record_api_metric("clob.create_and_post_order", time.time() - t0, ok=True)
            if not ok_fill:
                return False, fill_err
            return True, ""
        except PolyApiException as e:
            self._record_api_metric("clob.create_and_post_order", time.time() - t0, ok=False, status_code=self._extract_status_code(e))
            msg = str(e)
            low = msg.lower()
            if "invalid signature" in low:
                self.auth_broken = True
            return False, msg
        except Exception as e:
            self._record_api_metric("clob.create_and_post_order", time.time() - t0, ok=False, status_code=self._extract_status_code(e))
            return False, repr(e)

    def _order_options(self, *, for_sell: bool = False) -> Any:
        """Build order options with attribute access for py-clob-client compatibility."""
        payload = {
            "tick_size": str(self.meta.tick_size),
            "neg_risk": False,
            "fee_rate_bps": int(self.fee_rate_bps),
            "fee_rate": int(self.fee_rate_raw),
            "order_type": (self.sell_order_type if for_sell else self.order_type),
            "time_in_force": (self.sell_order_type if for_sell else self.order_type),
            "type": (self.sell_order_type if for_sell else self.order_type),
        }
        # Some client versions expect options.tick_size/options.neg_risk attributes.
        return SimpleNamespace(**payload)

    def _pick(self, obj: Any, name: str) -> Any:
        if isinstance(obj, dict):
            return obj.get(name)
        return getattr(obj, name, None)

    def _order_looks_filled(self, order: Any) -> Tuple[bool, str]:
        if not self.require_immediate_fill:
            return True, ""

        status = str(self._pick(order, "status") or self._pick(order, "state") or "").upper()
        filled = self._to_float_safe(self._pick(order, "filled") or self._pick(order, "filled_size") or self._pick(order, "filledSize"))
        size = self._to_float_safe(self._pick(order, "size") or self._pick(order, "original_size") or self._pick(order, "originalSize"))

        if status in {"FILLED", "MATCHED", "EXECUTED"}:
            return True, ""
        if filled is not None and size is not None and size > 0 and filled >= size:
            return True, ""

        order_id = self._pick(order, "orderID") or self._pick(order, "order_id") or self._pick(order, "id")
        if status in {"OPEN", "LIVE", "PENDING", "PLACED"}:
            return False, f"order_not_filled_immediately status={status} order_id={order_id}"

        if status:
            return False, f"order_not_confirmed_filled status={status} order_id={order_id}"

        # Unknown shape: assume not guaranteed filled, surface type for debugging.
        return False, f"order_fill_unknown shape={type(order).__name__}"

    def _to_float_safe(self, v: Any) -> Optional[float]:
        try:
            if v is None:
                return None
            return float(v)
        except Exception:
            return None

    def _buy_note(self, base: str, ask_px: Optional[float], submit_px: float) -> str:
        ask_txt = "-" if ask_px is None else f"{ask_px:.4f}"
        return f"{base} | ask={ask_txt} submit={submit_px:.4f}"

    def _is_allowed_original_arb_buy_price(self, price: float, *, allow_completion_discount: bool = False) -> bool:
        if not self._is_original_arb_mode():
            return True
        px = float(price)
        if 0.45 <= px <= 0.55:
            return True
        if allow_completion_discount and px < 0.45:
            return True
        return False

    def _sell_limit_price(self, bid: Optional[float], ask: Optional[float]) -> Optional[float]:
        if bid is None and ask is None:
            return None
        tick = max(0.001, self.meta.tick_size)
        under = self.sell_undercut_cents
        px: Optional[float]
        if self.sell_price_mode == "ask":
            px = ask if ask is not None else bid
        elif self.sell_price_mode == "ask_minus":
            base = ask if ask is not None else bid
            px = (base - under) if base is not None else None
        elif self.sell_price_mode == "bid_minus":
            base = bid if bid is not None else ask
            px = (base - under) if base is not None else None
        else:  # bid
            px = bid if bid is not None else ask
        if px is None:
            return None
        px = max(tick, min(0.999, px))
        # floor to tick
        steps = int(px / tick)
        px = max(tick, steps * tick)
        return px

    def _extract_wallet_debug(self, raw: Any) -> WalletDebug:
        def _pick(obj: Any, name: str) -> Any:
            if isinstance(obj, dict):
                return obj.get(name)
            return getattr(obj, name, None)

        bal = _pick(raw, "balance")
        if bal is None:
            bal = _pick(raw, "balance_decimal") or _pick(raw, "balanceDecimal")

        allowance = _pick(raw, "allowance")
        if allowance is None:
            allowance = _pick(raw, "allowance_decimal") or _pick(raw, "allowanceDecimal")

        available = _pick(raw, "available")
        if available is None:
            available = _pick(raw, "available_balance") or _pick(raw, "availableBalance")

        return WalletDebug(
            status="ok",
            balance=self._to_float_safe(bal),
            matic=None,
            allowance=self._to_float_safe(allowance),
            available=self._to_float_safe(available),
            detail=f"raw_type={type(raw).__name__}",
        )

    def _meets_min_order(self, price: float, qty: float) -> bool:
        return qty >= self.min_order_shares and (price * qty) >= self.min_order_usd

    def _settle_pnls(self, up_shares: float, down_shares: float, total_paid: float) -> Tuple[float, float]:
        return up_shares - total_paid, down_shares - total_paid

    def _can_buy_without_breaking_settlement_floor(self, delta_up: float, delta_down: float, added_paid: float) -> bool:
        cur_up, cur_down = self._settle_pnls(self.up_shares_bought, self.down_shares_bought, self.up_paid_total + self.down_paid_total)
        new_up, new_down = self._settle_pnls(
            self.up_shares_bought + delta_up,
            self.down_shares_bought + delta_down,
            self.up_paid_total + self.down_paid_total + added_paid,
        )
        # Keep worst-case settlement PnL non-decreasing and above configured floor.
        return min(new_up, new_down) >= self.settle_floor and min(new_up, new_down) >= min(cur_up, cur_down)

    def _can_buy_with_loss_limit(self, delta_up: float, delta_down: float, added_paid: float, loss_limit: float) -> bool:
        new_up, new_down = self._settle_pnls(
            self.up_shares_bought + delta_up,
            self.down_shares_bought + delta_down,
            self.up_paid_total + self.down_paid_total + added_paid,
        )
        return min(new_up, new_down) >= -max(0.0, loss_limit)

    def _micro_trend(self, side: str) -> float:
        data = list(self.flip_history[side])
        if len(data) < 6:
            return 0.0
        mids = [x[1] for x in data[-6:]]
        return mids[-1] - mids[0]

    def try_quant_hedge(self, books: TopOfBook, runtime_stats: RuntimeStats):
        if not self._can_open_new_buy():
            self._record_skip("hedge:max_trades")
            return
        if books.up_ask is None or books.dn_ask is None:
            self._record_skip("hedge:missing_ask")
            return

        guard = -self.hedge_minor_loss_limit
        cur_up, cur_down = runtime_stats.pnl_if_up_wins, runtime_stats.pnl_if_down_wins
        worst = min(cur_up, cur_down)

        # 1) Protective rebalance: buy whichever side is currently weaker in settlement payoff.
        if worst < guard:
            side = "UP" if cur_up < cur_down else "DOWN"
            ask = books.up_ask if side == "UP" else books.dn_ask
            ask_sz = (books.up_ask_sz or 0.0) if side == "UP" else (books.dn_ask_sz or 0.0)
            if ask is None or ask_sz <= 0:
                self._record_skip("hedge:no_liquidity")
                return
            c = ask * (1.0 + self.meta.taker_fee_rate)
            if c >= 0.999:
                self._record_skip("hedge:cost_too_high")
                return
            low_pnl = cur_up if side == "UP" else cur_down
            high_pnl = cur_down if side == "UP" else cur_up
            need = max(0.0, (guard - low_pnl) / max(1e-9, (1.0 - c)))
            cap_other = max(0.0, (high_pnl - guard) / max(1e-9, c))
            budget = self.remaining_budget()
            qty = min(need, cap_other, self.step_shares, ask_sz, self.remaining_session_shares(), budget / max(1e-9, c))
            if qty <= 0 or not self._meets_min_order(ask, qty):
                self._record_skip("hedge:rebalance_qty_zero")
                return
            delta_up, delta_dn = (qty, 0.0) if side == "UP" else (0.0, qty)
            added_paid = self.est_effective_cost(ask * qty)
            if not self._can_buy_with_loss_limit(delta_up, delta_dn, added_paid, self.hedge_minor_loss_limit):
                self._record_skip("hedge:guard_reject")
                return
            token = self.meta.token_ids[0] if side == "UP" else self.meta.token_ids[1]
            ok, err = self._post_buy(token, ask, qty, f"quant hedge rebalance {side}")
            ts = now_utc().astimezone().strftime("%H:%M:%S")
            self.log_action(TradeAction(ts, "BUY", side, qty, ask, self._buy_note(f"quant hedge rebalance {side}", ask, ask), ok, err))
            if ok:
                self._record_purchase(token, ask, qty)
                self.spent_est += added_paid
            return

        # 2) Optional convex upside add: only when guard buffer exists.
        buffer = worst - guard
        if buffer <= 0:
            self._record_skip("hedge:no_buffer")
            return
        trend_up = self._micro_trend("UP")
        trend_dn = self._micro_trend("DOWN")
        side = "UP" if trend_up > trend_dn else "DOWN"
        trend = max(trend_up, trend_dn)
        if trend <= max(self.meta.tick_size, 0.004):
            self._record_skip("hedge:trend_weak")
            return
        ask = books.up_ask if side == "UP" else books.dn_ask
        ask_sz = (books.up_ask_sz or 0.0) if side == "UP" else (books.dn_ask_sz or 0.0)
        if ask is None or ask_sz <= 0:
            self._record_skip("hedge:no_liquidity")
            return
        c = ask * (1.0 + self.meta.taker_fee_rate)
        budget = self.remaining_budget()
        risk_budget = buffer * self.hedge_upside_allocation
        if c <= 0:
            return
        qty = min(self.hedge_max_extra_shares, self.step_shares, ask_sz, self.remaining_session_shares(), budget / c, risk_budget / c)
        if qty <= 0 or not self._meets_min_order(ask, qty):
            self._record_skip("hedge:upside_qty_zero")
            return
        delta_up, delta_dn = (qty, 0.0) if side == "UP" else (0.0, qty)
        added_paid = self.est_effective_cost(ask * qty)
        if not self._can_buy_with_loss_limit(delta_up, delta_dn, added_paid, self.hedge_minor_loss_limit):
            self._record_skip("hedge:upside_guard_reject")
            return
        token = self.meta.token_ids[0] if side == "UP" else self.meta.token_ids[1]
        ok, err = self._post_buy(token, ask, qty, f"quant hedge upside add {side}")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "BUY", side, qty, ask, self._buy_note(f"quant hedge upside add {side}", ask, ask), ok, err))
        if ok:
            self._record_purchase(token, ask, qty)
            self.spent_est += added_paid

    def _fetch_order_by_id(self, order_id: str) -> Optional[Any]:
        if not self.authed_client or not order_id:
            return None
        candidates = [
            ("get_order", (order_id,)),
            ("get_order", ({"id": order_id},)),
            ("get_order", ({"order_id": order_id},)),
            ("get_order_status", (order_id,)),
            ("get_order_by_id", (order_id,)),
        ]
        for meth, args in candidates:
            fn = getattr(self.authed_client, meth, None)
            if not callable(fn):
                continue
            try:
                return fn(*args)
            except Exception:
                continue
        return None

    def _extract_order_id_from_err(self, err: str) -> Optional[str]:
        m = re.search(r"order_id=([0-9a-zA-Zx]+)", err or "")
        return m.group(1) if m else None

    def _queue_pending_fill_check(
        self,
        token_id: str,
        price: float,
        size: float,
        note: str,
        err: str,
        action_ref: Optional[TradeAction],
        *,
        pair_id: Optional[str] = None,
        pair_side: Optional[str] = None,
    ):
        order_id = self._extract_order_id_from_err(err)
        if not order_id:
            return
        if pair_id and pair_side in {"UP", "DOWN"}:
            state = self.pending_pair_unwinds.setdefault(
                pair_id,
                {
                    "created_ts": time.time(),
                    "unwound": False,
                    "mode": "instant_bundle",
                    "UP": {"filled": False},
                    "DOWN": {"filled": False},
                },
            )
            state[pair_side].update({"token_id": token_id, "price": price, "size": size, "order_id": order_id})
        self.pending_fill_checks.append(
            {
                "order_id": order_id,
                "token_id": token_id,
                "price": price,
                "size": size,
                "note": note,
                "created_ts": time.time(),
                "action_ref": action_ref,
                "credited_filled": 0.0,
                "pair_id": pair_id,
                "pair_side": pair_side,
            }
        )

    def _cancel_order_by_id(self, order_id: str) -> Tuple[bool, str]:
        if not self.live:
            return True, ""
        if not self.authed_client or not order_id:
            return False, "no_authed_client_or_order_id"
        candidates = [
            ("cancel", (order_id,)),
            ("cancel_order", (order_id,)),
            ("cancel_order", ({"id": order_id},)),
            ("cancel_order", ({"order_id": order_id},)),
            ("cancel_orders", ([order_id],)),
        ]
        for meth, args in candidates:
            fn = getattr(self.authed_client, meth, None)
            if not callable(fn):
                continue
            try:
                fn(*args)
                return True, ""
            except Exception as e:
                last_err = repr(e)
                continue
        return False, locals().get("last_err", "cancel_method_unavailable")

    def _extract_order_id_any(self, msg: str) -> Optional[str]:
        if not msg:
            return None
        for pat in [r"order_id=([0-9a-zA-Zx-]+)", r"orderID=([0-9a-zA-Zx-]+)", r"id=([0-9a-zA-Zx-]+)"]:
            m = re.search(pat, msg)
            if m:
                return m.group(1)
        return None

    def _available_qty_for_side(self, side: str) -> float:
        if side == "UP":
            if not self.live:
                return max(0.0, self.paper_up_qty)
            return max(0.0, self.last_positions_snapshot.up.size)
        if side == "DOWN":
            if not self.live:
                return max(0.0, self.paper_dn_qty)
            return max(0.0, self.last_positions_snapshot.down.size)
        return 0.0

    def _queue_unwind_sell_check(
        self,
        pair_id: str,
        side: str,
        token_id: str,
        order_id: str,
        requested_qty: float,
        action_ref: Optional[TradeAction] = None,
    ):
        if not order_id:
            return
        self.pending_unwind_sell_checks.append(
            {
                "pair_id": pair_id,
                "side": side,
                "token_id": token_id,
                "order_id": order_id,
                "requested_qty": max(0.0, float(requested_qty or 0.0)),
                "created_ts": time.time(),
                "last_retry_ts": 0.0,
                "action_ref": action_ref,
            }
        )

    def _queue_pending_risk_sell_check(
        self,
        side: str,
        token_id: str,
        order_id: str,
        requested_qty: float,
        price: float,
        reason: str,
        action_ref: Optional[TradeAction],
    ):
        if not order_id:
            return
        self.pending_risk_sell_checks.append(
            {
                "side": side,
                "token_id": token_id,
                "order_id": order_id,
                "requested_qty": max(0.0, float(requested_qty or 0.0)),
                "price": max(0.0, float(price or 0.0)),
                "reason": reason,
                "created_ts": time.time(),
                "action_ref": action_ref,
            }
        )

    def _recheck_pending_risk_sells(self):
        if not self.pending_risk_sell_checks:
            return
        now_ts = time.time()
        keep: List[Dict[str, Any]] = []
        for item in self.pending_risk_sell_checks:
            oid = str(item.get("order_id") or "")
            snap = self._fetch_order_by_id(oid)
            if snap is None:
                if (now_ts - float(item.get("created_ts") or now_ts)) < 60:
                    keep.append(item)
                continue

            status = str(self._pick(snap, "status") or self._pick(snap, "state") or "").upper()
            req = max(0.0, float(item.get("requested_qty") or 0.0))
            filled = self._to_float_safe(self._pick(snap, "filled") or self._pick(snap, "filled_size") or self._pick(snap, "filledSize")) or 0.0
            remaining = max(0.0, req - filled)
            ref = item.get("action_ref")
            prev_filled = max(0.0, float(item.get("credited_filled") or 0.0))
            delta_filled = max(0.0, filled - prev_filled)
            if delta_filled > 0:
                px = max(0.0, float(item.get("price") or 0.0))
                credit = max(0.0, px * delta_filled * (1.0 - self.meta.taker_fee_rate))
                self.spent_est = max(0.0, self.spent_est - credit)
            item["credited_filled"] = max(prev_filled, filled)
            is_filled = status in {"FILLED", "MATCHED", "EXECUTED"} or remaining <= 1e-9

            if is_filled:
                if isinstance(ref, TradeAction):
                    ref.ok = True
                    ref.err = ""
                    ref.note = f"{ref.note} | risk sell confirmed filled on recheck"
                continue

            if status in {"CANCELLED", "CANCELED", "REJECTED", "EXPIRED", "FAILED"}:
                if isinstance(ref, TradeAction):
                    ref.note = f"{ref.note} | final status {status}"
                continue

            if (now_ts - float(item.get("created_ts") or now_ts)) < 60:
                keep.append(item)

        self.pending_risk_sell_checks = keep

    def _recheck_pending_unwind_sells(self):
        if not self.pending_unwind_sell_checks:
            return
        now_ts = time.time()
        keep: List[Dict[str, Any]] = []
        for item in self.pending_unwind_sell_checks:
            oid = str(item.get("order_id") or "")
            pair_id = str(item.get("pair_id") or "")
            side = str(item.get("side") or "")
            pair = self.pending_pair_unwinds.get(pair_id)
            if isinstance(pair, dict) and pair.get("unwound"):
                continue
            token_id = str(item.get("token_id") or "")
            req = max(0.0, float(item.get("requested_qty") or 0.0))
            ref = item.get("action_ref")
            snap = self._fetch_order_by_id(oid)
            if snap is None:
                if (now_ts - float(item.get("created_ts") or now_ts)) < 60:
                    keep.append(item)
                continue

            status = str(self._pick(snap, "status") or self._pick(snap, "state") or "").upper()
            filled = self._to_float_safe(self._pick(snap, "filled") or self._pick(snap, "filled_size") or self._pick(snap, "filledSize")) or 0.0
            remaining = max(0.0, req - filled)
            if status in {"FILLED", "MATCHED", "EXECUTED"} or remaining <= 1e-9:
                pair = self.pending_pair_unwinds.get(pair_id)
                if isinstance(pair, dict):
                    pair["unwound"] = True
                if isinstance(ref, TradeAction):
                    ref.ok = True
                    ref.err = ""
                    ref.note = f"{ref.note} | unwind confirmed filled on recheck"
                continue

            if status in {"OPEN", "LIVE", "PENDING", "PLACED"} and (now_ts - float(item.get("created_ts") or now_ts)) < 10.0:
                keep.append(item)
                continue

            avail = self._available_qty_for_side(side)
            sell_qty = min(remaining, avail)
            if sell_qty <= 0:
                keep.append(item)
                continue
            if (now_ts - float(item.get("last_retry_ts") or 0.0)) < 4.0:
                keep.append(item)
                continue

            books = self._last_books
            bid = books.up_bid if (books and side == "UP") else (books.dn_bid if books else None)
            ask = books.up_ask if (books and side == "UP") else (books.dn_ask if books else None)
            sell_px = self._sell_limit_price(bid, ask)
            if sell_px is None:
                keep.append(item)
                continue
            ok, err = self._post_sell(token_id, sell_px, sell_qty, f"pair unwind remainder {side}")
            ts = now_utc().astimezone().strftime("%H:%M:%S")
            retry_action = TradeAction(ts, "SELL", side, sell_qty, sell_px, "pair unwind remainder retry", ok, err)
            self.log_action(retry_action)
            item["last_retry_ts"] = now_ts
            if ok:
                pair = self.pending_pair_unwinds.get(pair_id)
                if isinstance(pair, dict):
                    pair["unwound"] = True
                continue
            if "order_not_filled_immediately" in (err or ""):
                next_oid = self._extract_order_id_any(err or "")
                if next_oid:
                    item["order_id"] = next_oid
                    item["requested_qty"] = sell_qty
                    item["created_ts"] = now_ts
                    item["action_ref"] = retry_action
                    keep.append(item)
                    continue
            keep.append(item)
        self.pending_unwind_sell_checks = keep

    def _is_original_arb_mode(self) -> bool:
        return not any(
            [
                self.scalp_only_mode,
                self.upswing_only_mode,
                self.ml_mode,
                self.replication_mode,
                self.collect_mode,
                self.hedge_only_mode,
                self.gpt_mode,
                self.fortress_mode,
            ]
        )

    def _record_paper_sale(self, token_id: str, size: float):
        qty = max(0.0, float(size or 0.0))
        if qty <= 0:
            return
        if token_id == self.meta.token_ids[0]:
            held = max(0.0, self.paper_up_qty)
            if held <= 0:
                return
            sold = min(held, qty)
            avg = (self.paper_up_cost / held) if held > 0 else 0.0
            self.paper_up_qty = held - sold
            self.paper_up_cost = max(0.0, self.paper_up_cost - (avg * sold))
        elif token_id == self.meta.token_ids[1]:
            held = max(0.0, self.paper_dn_qty)
            if held <= 0:
                return
            sold = min(held, qty)
            avg = (self.paper_dn_cost / held) if held > 0 else 0.0
            self.paper_dn_qty = held - sold
            self.paper_dn_cost = max(0.0, self.paper_dn_cost - (avg * sold))

    def _attempt_pair_unwind(self, pair_id: str, *, reason: str = "timeout", fast_exit: bool = False):
        if not self._is_original_arb_mode():
            return
        pair = self.pending_pair_unwinds.get(pair_id)
        if not pair or pair.get("unwound"):
            return
        if pair.get("resolved"):
            return
        if any(str(x.get("pair_id") or "") == pair_id for x in self.pending_unwind_sell_checks):
            return
        up = pair.get("UP") or {}
        dn = pair.get("DOWN") or {}
        if bool(up.get("filled")) == bool(dn.get("filled")):
            return

        unwind_side = "UP" if bool(up.get("filled")) else "DOWN"
        unwind_leg = up if unwind_side == "UP" else dn
        stuck_leg = dn if unwind_side == "UP" else up
        token_id = str(unwind_leg.get("token_id") or "")
        qty = max(0.0, float(unwind_leg.get("size") or 0.0))
        if not token_id or qty <= 0:
            pair["unwound"] = True
            return
        next_try_ts = float(pair.get("next_unwind_try_ts") or 0.0)
        now_ts = time.time()
        if now_ts < next_try_ts:
            return

        avail = self._available_qty_for_side(unwind_side)
        qty = min(qty, avail)
        if qty <= 0:
            pair["next_unwind_try_ts"] = now_ts + 4.0
            self._record_skip(f"pair_unwind:no_balance:{unwind_side}")
            return

        books = self._last_books
        bid = books.up_bid if (books and unwind_side == "UP") else (books.dn_bid if books else None)
        ask = books.up_ask if (books and unwind_side == "UP") else (books.dn_ask if books else None)
        if fast_exit and bid is not None:
            tick = max(0.001, self.meta.tick_size)
            sell_px = max(tick, min(0.999, math.floor(bid / tick) * tick))
        else:
            sell_px = self._sell_limit_price(bid, ask)
        if sell_px is None:
            self._record_skip(f"pair_unwind:no_price:{unwind_side}")
            return

        stuck_order_id = str(stuck_leg.get("order_id") or "")
        if stuck_order_id:
            snap = self._fetch_order_by_id(stuck_order_id)
            if snap is not None:
                s_status = str(self._pick(snap, "status") or self._pick(snap, "state") or "").upper()
                s_filled = self._to_float_safe(self._pick(snap, "filled") or self._pick(snap, "filled_size") or self._pick(snap, "filledSize")) or 0.0
                s_size = self._to_float_safe(self._pick(snap, "size") or self._pick(snap, "original_size") or self._pick(snap, "originalSize"))
                s_expected = max(0.0, float(stuck_leg.get("size") or 0.0))
                s_cmp = s_size if (s_size is not None and s_size > 0) else s_expected
                stuck_is_filled = (s_status in {"FILLED", "MATCHED", "EXECUTED"}) or (s_cmp > 0 and s_filled >= s_cmp)
                if stuck_is_filled:
                    stuck_leg["filled"] = True
                    pair["resolved"] = True
                    pair["resolved_ts"] = now_ts
                    self.pair_fill_grace_until_ts = max(self.pair_fill_grace_until_ts, now_ts + 15.0)
                    self.logger.info("Skipping unwind because opposite leg filled before cancel; pair_id=%s order_id=%s status=%s", pair_id, stuck_order_id, s_status)
                    return
            c_ok, c_err = self._cancel_order_by_id(stuck_order_id)
            if c_ok:
                self.logger.info("Canceled unfilled paired leg before unwind sell; pair_id=%s order_id=%s", pair_id, stuck_order_id)
            else:
                self.logger.warning("Failed to cancel unfilled paired leg; pair_id=%s order_id=%s err=%s", pair_id, stuck_order_id, c_err)

        ok, err = self._post_sell(token_id, sell_px, qty, f"pair unwind {reason} {unwind_side}")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        note = "pair unwind (other leg not filled after 5s)"
        if reason == "price_drop":
            note = "pair unwind (other leg pending + filled leg dropped >=$0.10)"
        unwind_action = TradeAction(ts, "SELL", unwind_side, qty, sell_px, note, ok, err)
        self.log_action(unwind_action)
        if ok:
            pair["unwound"] = True
            self.pending_unwind_sell_checks = [x for x in self.pending_unwind_sell_checks if str(x.get("pair_id") or "") != pair_id]
        elif "order_not_filled_immediately" in (err or ""):
            sell_oid = self._extract_order_id_any(err or "")
            if sell_oid:
                self._queue_unwind_sell_check(pair_id, unwind_side, token_id, sell_oid, qty, action_ref=unwind_action)
                pair["next_unwind_try_ts"] = now_ts + 6.0
        else:
            pair["next_unwind_try_ts"] = now_ts + 8.0
        if ok:
            self.logger.info("Executed pair unwind sell; pair_id=%s reason=%s side=%s qty=%.4f px=%.4f", pair_id, reason, unwind_side, qty, sell_px)
        else:
            self.logger.warning("Pair unwind sell failed; pair_id=%s reason=%s side=%s err=%s", pair_id, reason, unwind_side, err)

    def _pair_unwind_price_drop_trigger(self, pair: Dict[str, Any]) -> Optional[Tuple[str, float, float]]:
        up = pair.get("UP") or {}
        dn = pair.get("DOWN") or {}
        if bool(up.get("filled")) == bool(dn.get("filled")):
            return None

        side = "UP" if bool(up.get("filled")) else "DOWN"
        leg = up if side == "UP" else dn
        entry = max(0.0, float(leg.get("price") or 0.0))
        if entry <= 0:
            return None

        books = self._last_books
        bid = books.up_bid if (books and side == "UP") else (books.dn_bid if books else None)
        ask = books.up_ask if (books and side == "UP") else (books.dn_ask if books else None)
        mark = bid if bid is not None else ask
        if mark is None:
            return None

        drop = entry - float(mark)
        if drop >= 0.10:
            return side, entry, float(mark)
        return None

    def _recheck_pending_fills(self):
        if (not self.pending_fill_checks) and (not self.pending_pair_unwinds) and (not self.pending_unwind_sell_checks) and (not self.pending_risk_sell_checks):
            return
        now_ts = time.time()
        if now_ts < self.next_pending_recheck_ts:
            return
        self.next_pending_recheck_ts = now_ts + self.pending_recheck_interval_s

        keep: List[Dict[str, Any]] = []
        for item in self.pending_fill_checks:
            oid = str(item.get("order_id") or "")
            snap = self._fetch_order_by_id(oid)
            if snap is None:
                if (now_ts - float(item.get("created_ts") or now_ts)) < 30:
                    keep.append(item)
                continue

            status = str(self._pick(snap, "status") or self._pick(snap, "state") or "").upper()
            filled = self._to_float_safe(self._pick(snap, "filled") or self._pick(snap, "filled_size") or self._pick(snap, "filledSize"))
            size = self._to_float_safe(self._pick(snap, "size") or self._pick(snap, "original_size") or self._pick(snap, "originalSize"))
            expected = float(item.get("size") or 0.0)
            ref = item.get("action_ref")
            pair_id = str(item.get("pair_id") or "")
            pair_side = str(item.get("pair_side") or "")

            is_filled = status in {"FILLED", "MATCHED", "EXECUTED"}
            if (not is_filled) and (filled is not None):
                cmp_size = size if (size is not None and size > 0) else expected
                if cmp_size > 0 and filled >= cmp_size:
                    is_filled = True

            if is_filled:
                token_id = str(item.get("token_id") or "")
                price = float(item.get("price") or 0.0)
                qty = float(item.get("size") or 0.0)
                self._record_purchase(token_id, price, qty)
                self.spent_est += self.est_effective_cost(price * qty)
                if pair_id and pair_side in {"UP", "DOWN"}:
                    state = self.pending_pair_unwinds.setdefault(pair_id, {"created_ts": now_ts, "unwound": False, "UP": {"filled": False}, "DOWN": {"filled": False}})
                    state[pair_side].update({"filled": True, "token_id": token_id, "price": price, "size": qty})
                    if bool((state.get("UP") or {}).get("filled")) and bool((state.get("DOWN") or {}).get("filled")):
                        state["resolved"] = True
                        state["resolved_ts"] = now_ts
                        self.pair_fill_grace_until_ts = max(self.pair_fill_grace_until_ts, now_ts + 15.0)
                if isinstance(ref, TradeAction):
                    ref.ok = True
                    ref.err = ""
                    ref.note = f"{ref.note} | confirmed filled on recheck"
                self.logger.info("Pending order recheck confirmed fill; order_id=%s status=%s", oid, status)
                continue

            if status in {"CANCELLED", "CANCELED", "REJECTED", "EXPIRED", "FAILED"}:
                if pair_id and pair_side in {"UP", "DOWN"}:
                    state = self.pending_pair_unwinds.setdefault(pair_id, {"created_ts": now_ts, "unwound": False, "UP": {"filled": False}, "DOWN": {"filled": False}})
                    state[pair_side].update({"filled": False, "final_status": status})
                if isinstance(ref, TradeAction):
                    ref.note = f"{ref.note} | final status {status}"
                continue

            if (now_ts - float(item.get("created_ts") or now_ts)) < 45:
                keep.append(item)

        self.pending_fill_checks = keep

        for pair_id, pair in list(self.pending_pair_unwinds.items()):
            if pair.get("unwound"):
                if (now_ts - float(pair.get("created_ts") or now_ts)) > 120:
                    self.pending_pair_unwinds.pop(pair_id, None)
                continue
            drop_trigger = self._pair_unwind_price_drop_trigger(pair)
            if drop_trigger is not None:
                side, entry, mark = drop_trigger
                if not pair.get("price_drop_triggered"):
                    pair["price_drop_triggered"] = True
                    self.logger.warning(
                        "Pair unwind emergency trigger: filled side %s dropped >=$0.10 while opposite leg pending; pair_id=%s entry=%.4f mark=%.4f",
                        side,
                        pair_id,
                        entry,
                        mark,
                    )
                self._attempt_pair_unwind(pair_id, reason="price_drop", fast_exit=True)
                continue
            age = now_ts - float(pair.get("created_ts") or now_ts)
            if age < 5.0:
                continue
            self._attempt_pair_unwind(pair_id)
        self._recheck_pending_unwind_sells()
        self._recheck_pending_risk_sells()

    def _net_imbalance(self, pos: PositionSnapshot) -> float:
        return pos.up.size - pos.down.size

    def _has_risky_imbalance(self, pos: PositionSnapshot) -> bool:
        return abs(self._net_imbalance(pos)) > self.max_net_imbalance_shares

    def _has_unresolved_exit_risk(self) -> bool:
        if self.flip_open and (self.flip_exit_fail_count.get("UP", 0) > 0 or self.flip_exit_fail_count.get("DOWN", 0) > 0):
            return True
        return False

    def _try_inventory_risk_sell(self, books: TopOfBook, pos: PositionSnapshot) -> bool:
        """Reduce oversized one-sided exposure by selling inventory before opening new buys."""
        self._ensure_runtime_guards()
        if self.auth_broken or self.funds_blocked or self.fee_broken:
            self._record_skip("risk_sell:trading_paused")
            return False
        net_imb = self._net_imbalance(pos)
        # Side-cap should apply to one-sided exposure, not fully hedged paired inventory.
        # Using unhedged sizes prevents selling one leg when UP and DOWN are matched.
        side_cap_eps = 1e-6
        over_up = max(0.0, pos.unhedged_up - self.max_side_position_shares - side_cap_eps)
        over_dn = max(0.0, pos.unhedged_down - self.max_side_position_shares - side_cap_eps)

        side: Optional[str] = None
        qty_need = 0.0
        reason = ""

        if over_up > 0 or over_dn > 0:
            if over_up >= over_dn:
                side = "UP"
                qty_need = over_up
            else:
                side = "DOWN"
                qty_need = over_dn
            reason = "side_cap"
        elif net_imb > self.max_net_imbalance_shares:
            side = "UP"
            qty_need = net_imb - self.max_net_imbalance_shares
            reason = "imbalance"
        elif net_imb < -self.max_net_imbalance_shares:
            side = "DOWN"
            qty_need = (-net_imb) - self.max_net_imbalance_shares
            reason = "imbalance"
        else:
            return False

        if side == "UP":
            bid = books.up_bid
            ask = books.up_ask
            bid_sz = books.up_bid_sz or 0.0
            held = pos.up.size
            avg = pos.up.avg_price
            token = self.meta.token_ids[0]
        else:
            bid = books.dn_bid
            ask = books.dn_ask
            bid_sz = books.dn_bid_sz or 0.0
            held = pos.down.size
            avg = pos.down.avg_price
            token = self.meta.token_ids[1]

        if bid is None or bid_sz <= 0 or held <= 0:
            self._record_skip("risk_sell:no_liquidity")
            return False
        if any(str(x.get("side") or "") == side for x in self.pending_risk_sell_checks):
            self._record_skip(f"risk_sell:pending:{side}")
            return False
        now_ts = time.time()
        if now_ts < float(self.risk_sell_next_retry_ts.get(side, 0.0)):
            self._record_skip(f"risk_sell:retry_wait:{side}")
            return False

        settle_gate = self.risk_sell_settle_gate.get(side, {"until": 0.0, "target": 0.0})
        gate_until = float(settle_gate.get("until") or 0.0)
        gate_target = max(0.0, float(settle_gate.get("target") or 0.0))
        if gate_until > 0:
            if held <= (gate_target + 0.05):
                if bool(settle_gate.get("set_rebuild")):
                    self.require_rebuild_after_risk_sell = True
                    self.post_risk_rebalance_cooldown_until_ts = max(
                        self.post_risk_rebalance_cooldown_until_ts,
                        time.time() + max(3.0, self.poll_s * 6.0),
                    )
                self.risk_sell_settle_gate[side] = {"until": 0.0, "target": 0.0}
            elif now_ts < gate_until:
                self._record_skip(f"risk_sell:settle_wait:{side}")
                return False
            else:
                self.risk_sell_settle_gate[side]["until"] = 0.0

        if now_ts < float(self.risk_sell_confirm_wait_until.get(side, 0.0)):
            if held <= (gate_target + 0.05):
                self.risk_sell_confirm_wait_until[side] = 0.0
            else:
                self._record_skip(f"risk_sell:confirm_wait:{side}")
                return False

        if time.time() < float(self.risk_sell_side_hold_until.get(side, 0.0)):
            self._record_skip(f"risk_sell:side_hold:{side}")
            return False

        pnl_per_share = bid - avg
        panic_mode = pnl_per_share <= -0.10
        if reason == "imbalance":
            if pnl_per_share < -self.inventory_stop_loss_cents:
                reason = "imbalance_stop"
            elif pnl_per_share >= self.inventory_take_profit_cents:
                reason = "imbalance_take"
        if panic_mode:
            reason = f"{reason}_panic" if reason else "panic"

        sell_px = self._sell_limit_price(bid, ask)
        if panic_mode and bid is not None:
            tick = max(0.001, self.meta.tick_size)
            panic_px = max(tick, min(0.999, bid - 0.01))
            sell_px = max(tick, math.floor(panic_px / tick) * tick)
        if sell_px is None:
            self._record_skip("risk_sell:no_price")
            return False
        qty_avail = min(held, self._available_qty_for_side(side))
        if panic_mode:
            qty = min(self.step_shares, qty_avail)
        else:
            qty = min(self.step_shares, qty_avail, bid_sz, max(0.0, qty_need))
        min_ok = ((qty >= 0.1 and (sell_px * qty) >= 0.05) if panic_mode else self._meets_min_order(sell_px, qty))
        if qty <= 0 or not min_ok:
            self._record_skip("risk_sell:min_order")
            return False

        ok, err = self._post_sell(token, sell_px, qty, f"risk rebalance sell {side} ({reason})")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        action = TradeAction(ts, "SELL", side, qty, sell_px, f"risk rebalance sell {side} ({reason})", ok, err)
        self.log_action(action)
        if not ok:
            self.risk_sell_next_retry_ts[side] = max(self.risk_sell_next_retry_ts.get(side, 0.0), time.time() + 2.5)
            if "order_not_filled_immediately" in (err or ""):
                sell_oid = self._extract_order_id_any(err or "")
                if sell_oid:
                    self._queue_pending_risk_sell_check(side, token, sell_oid, qty, sell_px, reason, action)
                    self.risk_sell_side_hold_until[side] = max(self.risk_sell_side_hold_until.get(side, 0.0), time.time() + 4.0)
                    self.risk_sell_settle_gate[side] = {
                        "until": time.time() + 12.0,
                        "target": max(0.0, held - qty),
                        "set_rebuild": 1.0,
                    }
                    self._record_skip("risk_sell:pending_recheck")
                    return False
            low = (err or "").lower()
            if "not enough balance" in low or "allowance" in low:
                # A previous sell likely filled and local positions are stale. Pause retries for this side.
                self.risk_sell_settle_gate[side] = {
                    "until": time.time() + 12.0,
                    "target": max(0.0, held - max(0.1, qty * 0.5)),
                    "set_rebuild": 1.0,
                }
                self.risk_sell_side_hold_until[side] = max(self.risk_sell_side_hold_until.get(side, 0.0), time.time() + 8.0)
                self._record_skip(f"risk_sell:balance_settle_wait:{side}")
                return False
            if "request exception" in low or "status_code=none" in low:
                # Network-level uncertainty: treat as potentially filled and wait for position settle before retrying.
                self.risk_sell_settle_gate[side] = {
                    "until": time.time() + 14.0,
                    "target": max(0.0, held - max(0.1, qty * 0.5)),
                    "set_rebuild": 1.0,
                }
                self.risk_sell_side_hold_until[side] = max(self.risk_sell_side_hold_until.get(side, 0.0), time.time() + 8.0)
                self._record_skip(f"risk_sell:network_settle_wait:{side}")
                return False
            self._record_skip("risk_sell:failed")
            return False

        credit = max(0.0, bid * qty * (1.0 - self.meta.taker_fee_rate))
        self.spent_est = max(0.0, self.spent_est - credit)
        self.post_risk_rebalance_cooldown_until_ts = max(
            self.post_risk_rebalance_cooldown_until_ts,
            time.time() + max(3.0, self.poll_s * 6.0),
        )
        self.risk_sell_side_hold_until[side] = max(self.risk_sell_side_hold_until.get(side, 0.0), time.time() + 4.0)
        self.risk_sell_settle_gate[side] = {
            "until": time.time() + 12.0,
            "target": max(0.0, held - qty),
            "set_rebuild": 1.0,
        }
        self.risk_sell_confirm_wait_until[side] = max(self.risk_sell_confirm_wait_until.get(side, 0.0), time.time() + 12.0)
        self.risk_sell_next_retry_ts[side] = max(self.risk_sell_next_retry_ts.get(side, 0.0), time.time() + 2.5)
        self.require_rebuild_after_risk_sell = True
        return True

    def _post_risk_rebalance_cooldown_remaining_s(self) -> float:
        return max(0.0, self.post_risk_rebalance_cooldown_until_ts - time.time())

    def refresh_wallet_debug(self, force: bool = False) -> WalletDebug:
        if (not force) and (time.time() - self._wallet_debug_last_ts < self.wallet_refresh_interval_s):
            return self.wallet_debug

        self._wallet_debug_last_ts = time.time()
        if not self.user_addr or not self.user_addr.startswith("0x"):
            self.wallet_debug = WalletDebug(status="error", detail="invalid user_addr for wallet diagnostics")
            return self.wallet_debug

        errors: List[str] = []
        urls = self.polygon_rpc_urls or ["https://polygon-rpc.com"]

        for rpc_url in urls:
            matic = None
            usdc = None
            local_errors: List[str] = []

            try:
                bal_hex = _rpc_call(rpc_url, "eth_getBalance", [self.user_addr, "latest"])
                wei = _rpc_hex_to_int(bal_hex)
                if wei is not None:
                    matic = wei / 1e18
            except Exception as e:
                local_errors.append(f"eth_getBalance {e!r}")

            try:
                data = _erc20_balance_of_data(self.user_addr)
                call_obj = {"to": POLYGON_USDC, "data": data}
                usdc_hex = _rpc_call(rpc_url, "eth_call", [call_obj, "latest"])
                raw = _rpc_hex_to_int(usdc_hex)
                if raw is not None:
                    usdc = raw / 1e6
            except Exception as e:
                local_errors.append(f"usdc_balance {e!r}")

            if matic is not None or usdc is not None:
                self.wallet_debug = WalletDebug(
                    status="ok_rpc",
                    balance=usdc,
                    matic=matic,
                    allowance=None,
                    available=None,
                    detail=f"rpc={rpc_url}",
                )
                if self.live and (not self.ml_mode) and usdc is not None and usdc >= 0:
                    self.max_spend_usd = float(usdc)
                    if (self._last_wallet_budget_value is None) or (abs(self._last_wallet_budget_value - self.max_spend_usd) >= 0.01):
                        self.logger.info("Max spend synced to wallet USDC balance: %.4f", self.max_spend_usd)
                        self._last_wallet_budget_value = self.max_spend_usd
                return self.wallet_debug

            errors.extend([f"{rpc_url}: {x}" for x in local_errors])

        combined = "; ".join(errors[-3:]) if errors else "wallet rpc probes failed"
        status = "rpc_auth_error" if "401" in combined or "Unauthorized" in combined else "error"
        self.wallet_debug = WalletDebug(status=status, detail=combined)
        return self.wallet_debug

    def _post_buy(self, token_id: str, price: float, size: float, note: str) -> Tuple[bool, str]:
        allow_completion_discount = "complete bundles" in (note or "").lower()
        if not self._is_allowed_original_arb_buy_price(price, allow_completion_discount=allow_completion_discount):
            return False, "price_band_reject"
        if not self.live:
            # Paper mode: always "fills"
            self._record_paper_fill(token_id, price, size)
            return True, ""
        if not self.authed_client:
            return False, "No authed client"
        if self.auth_broken:
            return False, "Auth disabled after INVALID_SIGNATURE (restart with SIGNATURE_TYPE=0 for regular wallets)"
        if self.funds_blocked:
            return False, "Trading paused after insufficient balance/allowance (check wallet diagnostics)"
        if self.fee_broken:
            return False, "Trading paused after repeated invalid fee-rate errors"
        t0 = time.time()
        try:
            # Use create_and_post_order (docs show this pattern) :contentReference[oaicite:8]{index=8}
            order = self.authed_client.create_and_post_order(
                self._order_args(token_id, price, size),
                self._order_options(),
            )
            ok_fill, fill_err = self._order_looks_filled(order)
            if not ok_fill:
                self._record_api_metric("clob.create_and_post_order", time.time() - t0, ok=True)
                return False, fill_err
            # Not printing order details to avoid leaking anything sensitive
            self._record_api_metric("clob.create_and_post_order", time.time() - t0, ok=True)
            return True, ""
        except PolyApiException as e:
            self._record_api_metric("clob.create_and_post_order", time.time() - t0, ok=False, status_code=self._extract_status_code(e))
            # PolyApiException carries status_code and message
            msg = str(e)
            low = msg.lower()
            if "invalid fee rate" in low:
                m = re.search(r"fee:\s*(\d+)", msg)
                required_raw = parse_intish(m.group(1), self.fee_rate_raw) if m else self.fee_rate_raw
                required_raw = max(1, required_raw)
                required_bps = required_raw
                self.logger.warning(
                    "Invalid fee rate detected; retrying once with fee_rate_raw=%s fee_rate_bps=%s",
                    required_raw,
                    required_bps,
                )
                self.fee_rate_raw = required_raw
                self.fee_rate_bps = required_bps
                try:
                    retry_order = self.authed_client.create_and_post_order(
                        self._order_args(token_id, price, size),
                        self._order_options(),
                    )
                    ok_fill, fill_err = self._order_looks_filled(retry_order)
                    if not ok_fill:
                        return False, fill_err
                    return True, ""
                except Exception as retry_err:
                    msg = repr(retry_err)
                    low = msg.lower()

            if "invalid fee rate" in low:
                self.fee_error_count += 1
                if self.fee_error_count >= 3:
                    self.fee_broken = True
                    self.logger.error("Trading paused for this run because fee-rate config is repeatedly rejected by API.")
            if "invalid signature" in low:
                self.auth_broken = True
                if not self.invalid_sig_hint_logged:
                    self.invalid_sig_hint_logged = True
                    self.logger.error(
                        "Server returned INVALID_SIGNATURE. If this is a regular wallet (not proxy/safe), use SIGNATURE_TYPE=0 and remove FUNDER/FUNDER_ADDRESS."
                    )
            if "not enough balance" in low or "allowance" in low:
                self.funds_blocked = True
                self.logger.error("Server returned insufficient balance/allowance. Trading will pause; check displayed wallet diagnostics.")
                self.refresh_wallet_debug(force=True)
            return False, msg
        except Exception as e:
            self._record_api_metric("clob.create_and_post_order", time.time() - t0, ok=False, status_code=self._extract_status_code(e))
            self.logger.exception("post_buy_failed")
            return False, repr(e)

    def try_instant_bundle(self, books: TopOfBook, pos: PositionSnapshot):
        if not self._can_open_new_buy():
            self._record_skip("buy:max_trades")
            return
        # Need both asks
        if books.up_ask is None or books.dn_ask is None:
            return

        if self._has_risky_imbalance(pos):
            self._record_skip("instant:risky_imbalance")
            return

        ask_sum = books.up_ask + books.dn_ask
        if ask_sum > 0.98:
            self._record_skip("instant:ask_sum_above_98c")
            return
        eff_cost = self.est_effective_cost(ask_sum)
        profit_per = 1.0 - eff_cost

        self.best_profit_per_bundle = max(self.best_profit_per_bundle, profit_per)
        self.best_cost_seen = min(self.best_cost_seen, eff_cost)

        # Cap by available ask sizes
        max_bundles_by_book = min(books.up_ask_sz or 0.0, books.dn_ask_sz or 0.0)
        if max_bundles_by_book <= 0:
            self._record_skip("instant:book_liquidity")
            return

        # Cap by budget
        budget = self.remaining_budget()
        if budget <= 0:
            self._record_skip("instant:budget")
            return
        max_bundles_by_budget = budget / self.est_effective_cost(ask_sum)
        bundles = min(max_bundles_by_book, max_bundles_by_budget)

        # Only trade if edge is good
        if profit_per < self.effective_min_edge():
            self._record_skip("instant:min_edge")
            return

        # Don’t spam tiny fills
        bundles = min(bundles, self.step_shares)
        bundles = self._limit_buy_qty_by_session(bundles)
        if bundles <= 0:
            self._record_skip("instant:session_cap")
            self._record_skip("instant:zero_qty")
            return
        if not self._meets_min_order(books.up_ask, bundles) or not self._meets_min_order(books.dn_ask, bundles):
            self._record_skip("instant:min_order")
            return
        added_paid = self.est_effective_cost(books.up_ask * bundles) + self.est_effective_cost(books.dn_ask * bundles)
        if not self._can_buy_without_breaking_settlement_floor(bundles, bundles, added_paid):
            self._record_skip("instant:settlement_guard")
            return

        # If combined bundle ask is very favorable (<= $0.98), nudge BOTH legs by +$0.005.
        # Only do this when tick size supports half-cent increments exactly; otherwise skip
        # to avoid rounding up to +$0.01 and accidentally paying ~1.00 total.
        up_buy_px = books.up_ask
        dn_buy_px = books.dn_ask
        if ask_sum <= 0.98:
            tick = max(0.001, self.meta.tick_size)
            half_cent = 0.005
            half_cent_steps = half_cent / tick
            half_cent_supported = abs(half_cent_steps - round(half_cent_steps)) < 1e-9
            if not half_cent_supported:
                self._record_skip("instant:half_cent_not_supported")
                return

            up_n = (books.up_ask or 0.0) + half_cent
            dn_n = (books.dn_ask or 0.0) + half_cent
            up_n = min(0.999, max(tick, up_n))
            dn_n = min(0.999, max(tick, dn_n))
            up_buy_px = min(0.999, math.ceil(up_n / tick) * tick)
            dn_buy_px = min(0.999, math.ceil(dn_n / tick) * tick)

            if (up_buy_px + dn_buy_px) >= 1.0:
                self._record_skip("instant:nudged_sum_ge_1")
                return

        if (not self._is_allowed_original_arb_buy_price(up_buy_px)) or (not self._is_allowed_original_arb_buy_price(dn_buy_px)):
            self._record_skip("instant:price_band")
            return

        self.opps_met += 1
        # Execute two buys (not atomic)
        pair_id = f"instant-{int(time.time() * 1000)}-{self.executed_trade_count}"
        ok1, err1 = self._post_buy(self.meta.token_ids[0], up_buy_px, bundles, "instant bundle")
        ok2, err2 = self._post_buy(self.meta.token_ids[1], dn_buy_px, bundles, "instant bundle")

        ts = now_utc().astimezone().strftime("%H:%M:%S")
        a1 = TradeAction(ts, "BUY", "UP", bundles, up_buy_px, self._buy_note("instant bundle", books.up_ask, up_buy_px), ok1, err1)
        a2 = TradeAction(ts, "BUY", "DOWN", bundles, dn_buy_px, self._buy_note("instant bundle", books.dn_ask, dn_buy_px), ok2, err2)
        self.log_action(a1)
        self.log_action(a2)
        if (not ok1) and ("order_not_filled_immediately" in (err1 or "")):
            self._queue_pending_fill_check(
                self.meta.token_ids[0],
                up_buy_px,
                bundles,
                "instant bundle",
                err1,
                a1,
                pair_id=pair_id,
                pair_side="UP",
            )
        if (not ok2) and ("order_not_filled_immediately" in (err2 or "")):
            self._queue_pending_fill_check(
                self.meta.token_ids[1],
                dn_buy_px,
                bundles,
                "instant bundle",
                err2,
                a2,
                pair_id=pair_id,
                pair_side="DOWN",
            )

        if ok1 != ok2:
            pair_state = self.pending_pair_unwinds.setdefault(
                pair_id,
                {
                    "created_ts": time.time(),
                    "unwound": False,
                    "mode": "instant_bundle",
                    "UP": {"filled": False},
                    "DOWN": {"filled": False},
                },
            )
            pair_state["UP"].update({"token_id": self.meta.token_ids[0], "price": up_buy_px, "size": bundles, "filled": bool(ok1)})
            pair_state["DOWN"].update({"token_id": self.meta.token_ids[1], "price": dn_buy_px, "size": bundles, "filled": bool(ok2)})

        if ok1:
            self._record_purchase(self.meta.token_ids[0], up_buy_px, bundles)
            self.spent_est += self.est_effective_cost(up_buy_px * bundles)
        if ok2:
            self._record_purchase(self.meta.token_ids[1], dn_buy_px, bundles)
            self.spent_est += self.est_effective_cost(dn_buy_px * bundles)

        # Any one-leg mismatch is dangerous; force rebalance-only behavior until inventory is leveled.
        if ok1 != ok2:
            self.rebalance_only_mode = True

    def try_complete_from_inventory(self, books: TopOfBook, pos: PositionSnapshot):
        if self.require_rebuild_after_risk_sell:
            self._record_skip("complete:reset_after_risk_sell")
            return
        if self._post_risk_rebalance_cooldown_remaining_s() > 0:
            self._record_skip("complete:post_risk_rebalance_cooldown")
            return
        if not self._can_open_new_buy():
            self._record_skip("buy:max_trades")
            return
        edge_target = self.effective_min_edge()
        # If you have unhedged UP, try buying DOWN to complete
        if books.dn_ask is not None and pos.unhedged_up > 0:
            held_cost = pos.up.avg_price
            cost_per = held_cost + books.dn_ask
            eff_cost = self.est_effective_cost(cost_per)
            profit_per = 1.0 - eff_cost
            if profit_per >= edge_target:
                budget = self.remaining_budget()
                if budget > 0:
                    max_by_budget = budget / self.est_effective_cost(books.dn_ask)
                    qty = min(pos.unhedged_up, books.dn_ask_sz or 0.0, max_by_budget, self.step_shares)
                    qty = self._limit_buy_qty_by_session(qty)
                    if qty > 0 and self._meets_min_order(books.dn_ask, qty):
                        added_paid = self.est_effective_cost(books.dn_ask * qty)
                        if not self._can_buy_without_breaking_settlement_floor(0.0, qty, added_paid):
                            self._record_skip("complete_down:settlement_guard")
                            return
                        if not self._is_allowed_original_arb_buy_price(books.dn_ask, allow_completion_discount=True):
                            self._record_skip("complete_down:price_band")
                        else:
                            ok, err = self._post_buy(self.meta.token_ids[1], books.dn_ask, qty, "complete bundles")
                            ts = now_utc().astimezone().strftime("%H:%M:%S")
                            action = TradeAction(ts, "BUY", "DOWN", qty, books.dn_ask, self._buy_note("complete bundles", books.dn_ask, books.dn_ask), ok, err)
                            self.log_action(action)
                            if (not ok) and ("order_not_filled_immediately" in (err or "")):
                                self._queue_pending_fill_check(self.meta.token_ids[1], books.dn_ask, qty, "complete bundles", err, action)
                            if ok:
                                self._record_purchase(self.meta.token_ids[1], books.dn_ask, qty)
                                self.spent_est += self.est_effective_cost(books.dn_ask * qty)

        # If you have unhedged DOWN, try buying UP to complete
        if books.up_ask is not None and pos.unhedged_down > 0:
            held_cost = pos.down.avg_price
            cost_per = held_cost + books.up_ask
            eff_cost = self.est_effective_cost(cost_per)
            profit_per = 1.0 - eff_cost
            if profit_per >= edge_target:
                budget = self.remaining_budget()
                if budget > 0:
                    max_by_budget = budget / self.est_effective_cost(books.up_ask)
                    qty = min(pos.unhedged_down, books.up_ask_sz or 0.0, max_by_budget, self.step_shares)
                    qty = self._limit_buy_qty_by_session(qty)
                    if qty > 0 and self._meets_min_order(books.up_ask, qty):
                        added_paid = self.est_effective_cost(books.up_ask * qty)
                        if not self._can_buy_without_breaking_settlement_floor(qty, 0.0, added_paid):
                            self._record_skip("complete_up:settlement_guard")
                            return
                        if not self._is_allowed_original_arb_buy_price(books.up_ask, allow_completion_discount=True):
                            self._record_skip("complete_up:price_band")
                        else:
                            ok, err = self._post_buy(self.meta.token_ids[0], books.up_ask, qty, "complete bundles")
                            ts = now_utc().astimezone().strftime("%H:%M:%S")
                            action = TradeAction(ts, "BUY", "UP", qty, books.up_ask, self._buy_note("complete bundles", books.up_ask, books.up_ask), ok, err)
                            self.log_action(action)
                            if (not ok) and ("order_not_filled_immediately" in (err or "")):
                                self._queue_pending_fill_check(self.meta.token_ids[0], books.up_ask, qty, "complete bundles", err, action)
                            if ok:
                                self._record_purchase(self.meta.token_ids[0], books.up_ask, qty)
                                self.spent_est += self.est_effective_cost(books.up_ask * qty)

    def try_build_inventory(self, books: TopOfBook, pos: PositionSnapshot):
        if not self._can_open_new_buy():
            self._record_skip("buy:max_trades")
            return
        if not self.allow_inventory_build:
            self._record_skip("build:disabled")
            return
        tte = self.time_to_end_s()
        if tte is not None and tte <= 60:
            self._record_skip("build:near_expiry")
            return  # stop inventory building near expiry

        budget = self.remaining_budget()
        if budget <= 0:
            self._record_skip("build:budget")
            return

        # Approx unhedged USD exposure (using avg prices)
        unhedged_usd = pos.unhedged_up * pos.up.avg_price + pos.unhedged_down * pos.down.avg_price
        if unhedged_usd >= self.unhedged_usd_max:
            self._record_skip("build:unhedged_limit")
            return

        # Choose cheapest ask
        candidates = []
        if books.up_ask is not None and (books.up_ask_sz or 0.0) > 0:
            candidates.append(("UP", books.up_ask, books.up_ask_sz or 0.0, self.meta.token_ids[0]))
        if books.dn_ask is not None and (books.dn_ask_sz or 0.0) > 0:
            candidates.append(("DOWN", books.dn_ask, books.dn_ask_sz or 0.0, self.meta.token_ids[1]))
        if not candidates:
            self._record_skip("build:no_candidates")
            return

        side, px, sz_avail, token = sorted(candidates, key=lambda x: x[1])[0]
        if px > self.build_max:
            self._record_skip("build:price_too_high")
            return

        max_by_budget = budget / self.est_effective_cost(px)
        qty = min(self.step_shares, sz_avail, max_by_budget)
        qty = self._limit_buy_qty_by_session(qty)
        if qty <= 0:
            self._record_skip("build:session_cap")
            self._record_skip("build:zero_qty")
            return
        if not self._meets_min_order(px, qty):
            self._record_skip("build:min_order")
            return

        added_paid = self.est_effective_cost(px * qty)
        delta_up, delta_dn = (qty, 0.0) if side == "UP" else (0.0, qty)
        if not self._can_buy_without_breaking_settlement_floor(delta_up, delta_dn, added_paid):
            # Inventory-build is intentionally allowed to take bounded one-sided risk
            # as long as projected worst-case settlement loss stays within unhedged_usd_max.
            if not self._can_buy_with_loss_limit(delta_up, delta_dn, added_paid, self.unhedged_usd_max):
                self._record_skip("build:settlement_guard")
                return

        if not self._is_allowed_original_arb_buy_price(px):
            self._record_skip("build:price_band")
            return

        ok, err = self._post_buy(token, px, qty, "build inventory")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        action = TradeAction(ts, "BUY", side, qty, px, self._buy_note("build inventory", px, px), ok, err)
        self.log_action(action)
        if (not ok) and ("order_not_filled_immediately" in (err or "")):
            self._queue_pending_fill_check(token, px, qty, "build inventory", err, action)
        if ok:
            self._record_purchase(token, px, qty)
            self.spent_est += self.est_effective_cost(px * qty)
            self.require_rebuild_after_risk_sell = False

    def _rpc_json(self, url: str, payload: Dict[str, Any], timeout_s: float = 2.5) -> Optional[Dict[str, Any]]:
        try:
            r = requests.post(url, json=payload, timeout=timeout_s)
            r.raise_for_status()
            data = r.json()
            if isinstance(data, dict):
                return data
        except Exception:
            return None
        return None

    def _eth_call_hex(self, to_addr: str, data_hex: str) -> Optional[str]:
        payload = {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "eth_call",
            "params": [
                {"to": to_addr, "data": data_hex},
                "latest",
            ],
        }
        for rpc in self.polygon_rpc_urls:
            out = self._rpc_json(rpc, payload)
            if not out:
                continue
            result = out.get("result")
            if isinstance(result, str) and result.startswith("0x") and len(result) > 2:
                return result
        return None

    def _start_btc_ws_feed(self):
        if self.btc_ws_started or (not self.btc_ws_enabled):
            return
        self.btc_ws_started = True

        def worker():
            while True:
                try:
                    def on_message(_ws, message):
                        try:
                            d = json.loads(message)
                            px = None
                            if isinstance(d, dict):
                                if "p" in d:
                                    px = parse_floatish(str(d.get("p")), 0.0)
                                elif "c" in d:
                                    px = parse_floatish(str(d.get("c")), 0.0)
                            if px and px > 0:
                                now_ts = time.time()
                                srv_ts = 0.0
                                if isinstance(d.get("T"), (int, float)):
                                    srv_ts = float(d.get("T")) / 1000.0
                                elif isinstance(d.get("E"), (int, float)):
                                    srv_ts = float(d.get("E")) / 1000.0
                                self._last_btc_price = px
                                self._last_btc_fetch_ts = now_ts
                                self._last_btc_server_ts = srv_ts if srv_ts > 0 else now_ts
                                self.btc_price_source = "binance_ws"
                                self.btc_spot_history.append((now_ts, px))
                                self.btc_ws_last_update_ts = now_ts
                                if self.btc_market_open_price is None:
                                    self.btc_market_open_price = px
                        except Exception as e:
                            self.btc_ws_failure_detail = repr(e)

                    def on_error(_ws, err):
                        self.btc_ws_failure_detail = str(err)

                    app = websocket.WebSocketApp(self.btc_ws_url, on_message=on_message, on_error=on_error)
                    app.run_forever(ping_interval=20, ping_timeout=10)
                except Exception as e:
                    self.btc_ws_failure_detail = repr(e)
                time.sleep(1.0)

        t = threading.Thread(target=worker, daemon=True)
        t.start()

    def _fetch_fast_btc_spot(self) -> Optional[float]:
        urls = [
            ("https://api.binance.com/api/v3/aggTrades", {"symbol": "BTCUSDT", "limit": 1}, "binance_agg_fast"),
            ("https://api.binance.com/api/v3/ticker/price", {"symbol": "BTCUSDT"}, "binance_fast"),
            ("https://api.coinbase.com/v2/prices/BTC-USD/spot", {}, "coinbase_fast"),
        ]
        for url, params, src in urls:
            try:
                r = requests.get(url, params=params, timeout=self.btc_fast_probe_timeout_s)
                r.raise_for_status()
                data = r.json()
                px: Optional[float] = None
                server_ts = 0.0
                date_hdr = r.headers.get("Date")
                if date_hdr:
                    try:
                        server_ts = parsedate_to_datetime(date_hdr).timestamp()
                    except Exception:
                        pass
                if isinstance(data, list) and data and isinstance(data[0], dict):
                    row = data[0]
                    if "p" in row:
                        px = parse_floatish(str(row.get("p")), 0.0)
                    if isinstance(row.get("T"), (int, float)):
                        server_ts = float(row.get("T")) / 1000.0
                if isinstance(data, dict) and "price" in data:
                    px = parse_floatish(str(data.get("price")), 0.0)
                elif isinstance(data, dict) and "data" in data:
                    px = parse_floatish(str((data.get("data") or {}).get("amount")), 0.0)
                if px and px > 0:
                    self.btc_price_source = src
                    self._last_btc_server_ts = server_ts if server_ts > 0 else self._last_btc_server_ts
                    return px
            except Exception:
                continue
        return None

    def _fetch_chainlink_btc_spot(self) -> Optional[float]:
        if self.chainlink_decimals is None:
            dec_hex = self._eth_call_hex(CHAINLINK_BTC_USD_FEED_POLYGON, CHAINLINK_DECIMALS_SELECTOR)
            if dec_hex:
                try:
                    self.chainlink_decimals = int(dec_hex, 16)
                except Exception:
                    self.chainlink_decimals = 8
            else:
                self.chainlink_decimals = 8

        latest_hex = self._eth_call_hex(CHAINLINK_BTC_USD_FEED_POLYGON, CHAINLINK_LATEST_ROUND_DATA_SELECTOR)
        if not latest_hex:
            return None
        raw = latest_hex[2:]
        if len(raw) < 64 * 5:
            return None
        # latestRoundData returns (roundId, answer, startedAt, updatedAt, answeredInRound)
        answer_hex = raw[64:128]
        updated_at_hex = raw[192:256]
        try:
            updated_at = int(updated_at_hex, 16)
            if updated_at > 0:
                self.chainlink_last_updated_at = updated_at
            answer_int = int(answer_hex, 16)
            if answer_int >= (1 << 255):
                answer_int -= (1 << 256)
            if answer_int <= 0:
                return None
            dec = self.chainlink_decimals if self.chainlink_decimals is not None else 8
            return float(answer_int) / float(10 ** dec)
        except Exception:
            return None

    def _fetch_btc_spot(self, force: bool = False) -> Optional[float]:
        now_ts = time.time()
        if (not force) and self._last_btc_price is not None and (now_ts - self._last_btc_fetch_ts) < self.btc_fetch_min_interval_s:
            return self._last_btc_price

        # Prefer websocket BTC ticks (lowest latency) across modes.
        if self.btc_prefer_ws:
            self._start_btc_ws_feed()
            if self._last_btc_price is not None and self.btc_price_source == "binance_ws" and (now_ts - self.btc_ws_last_update_ts) <= 2.0:
                return self._last_btc_price

        if self.btc_low_latency_mode:
            fast_px = self._fetch_fast_btc_spot()
            if fast_px and fast_px > 0:
                self._last_btc_fetch_ts = now_ts
                if self._last_btc_server_ts <= 0:
                    self._last_btc_server_ts = now_ts
                self._last_btc_price = fast_px
                self.btc_spot_history.append((now_ts, fast_px))
                if self.btc_market_open_price is None:
                    self.btc_market_open_price = fast_px
                return fast_px

        chainlink_px = self._fetch_chainlink_btc_spot()
        chainlink_age = None
        if self.chainlink_last_updated_at:
            chainlink_age = max(0.0, now_ts - float(self.chainlink_last_updated_at))

        fallback_price = None
        need_fallback_probe = (not chainlink_px) or (chainlink_age is not None and chainlink_age >= self.chainlink_stale_after_s)
        if need_fallback_probe:
            urls = [
                ("https://api.coingecko.com/api/v3/simple/price", {"ids": "bitcoin", "vs_currencies": "usd"}),
                ("https://api.binance.com/api/v3/ticker/price", {"symbol": "BTCUSDT"}),
            ]
            for url, params in urls:
                try:
                    r = requests.get(url, params=params, timeout=1.2)
                    r.raise_for_status()
                    data = r.json()
                    price: Optional[float] = None
                    if isinstance(data, dict) and "bitcoin" in data:
                        price = parse_floatish(str(data.get("bitcoin", {}).get("usd")), 0.0)
                    elif isinstance(data, dict) and "price" in data:
                        price = parse_floatish(str(data.get("price")), 0.0)
                    if price and price > 0:
                        fallback_price = price
                        break
                except Exception:
                    continue

        chosen_price = None
        chosen_source = "n/a"
        if chainlink_px and chainlink_px > 0:
            use_fallback = fallback_price is not None and chainlink_age is not None and chainlink_age >= self.chainlink_stale_after_s
            if use_fallback:
                chosen_price = fallback_price
                chosen_source = f"chainlink_stale({chainlink_age:.1f}s)+fallback"
            else:
                chosen_price = chainlink_px
                chosen_source = "chainlink"
        elif fallback_price is not None:
            chosen_price = fallback_price
            chosen_source = "fallback"

        if chosen_price and chosen_price > 0:
            self._last_btc_fetch_ts = now_ts
            if chosen_source == "chainlink" and self.chainlink_last_updated_at:
                self._last_btc_server_ts = float(self.chainlink_last_updated_at)
            elif self._last_btc_server_ts <= 0:
                self._last_btc_server_ts = now_ts
            self._last_btc_price = chosen_price
            self.btc_price_source = chosen_source
            self.btc_spot_history.append((now_ts, chosen_price))
            if self.btc_market_open_price is None:
                self.btc_market_open_price = chosen_price
            return chosen_price
        return self._last_btc_price

    def _fetch_btc_price_at_ts(self, ts_epoch: float) -> Optional[float]:
        # Prefer exchange candle open exactly at/after the target second.
        try:
            r = requests.get(
                "https://api.binance.com/api/v3/klines",
                params={"symbol": "BTCUSDT", "interval": "1m", "startTime": int(ts_epoch * 1000), "limit": 1},
                timeout=2.5,
            )
            r.raise_for_status()
            data = r.json()
            if isinstance(data, list) and data and isinstance(data[0], list) and len(data[0]) >= 2:
                px = parse_floatish(str(data[0][1]), 0.0)
                if px > 0:
                    return px
        except Exception:
            pass

        # Fallback: nearest Coingecko tick around target.
        try:
            r = requests.get(
                "https://api.coingecko.com/api/v3/coins/bitcoin/market_chart/range",
                params={
                    "vs_currency": "usd",
                    "from": int(max(0, ts_epoch - 90)),
                    "to": int(ts_epoch + 90),
                },
                timeout=2.5,
            )
            r.raise_for_status()
            data = r.json()
            pts = data.get("prices") if isinstance(data, dict) else None
            if isinstance(pts, list) and pts:
                best = None
                for item in pts:
                    if not (isinstance(item, list) and len(item) >= 2):
                        continue
                    t = float(item[0]) / 1000.0
                    p = parse_floatish(str(item[1]), 0.0)
                    if p <= 0:
                        continue
                    d = abs(t - ts_epoch)
                    if best is None or d < best[0]:
                        best = (d, p)
                if best is not None:
                    return best[1]
        except Exception:
            pass
        return None

    def _sync_market_open_price(self):
        if self.btc_market_open_price is not None:
            return
        if not self.meta.start_dt_utc:
            # Fallback for unknown start: use first available spot.
            px = self._fetch_btc_spot(force=True)
            if px and px > 0:
                self.btc_market_open_price = px
                self.btc_market_open_source = "fallback_unknown_start"
            return

        start_ts = self.meta.start_dt_utc.timestamp()
        now_ts = time.time()
        if now_ts < start_ts:
            # Market has not opened yet; keep waiting.
            return

        # If we joined after market open, backfill from historical near start boundary.
        if (now_ts - start_ts) > 1.0:
            hist = self._fetch_btc_price_at_ts(start_ts)
            if hist and hist > 0:
                self.btc_market_open_price = hist
                self.btc_market_open_source = "historical_at_start"
                return

        # If right on/near boundary (or historical unavailable), capture live spot now.
        px = self._fetch_btc_spot(force=True)
        if px and px > 0:
            self.btc_market_open_price = px
            self.btc_market_open_source = "captured_at_start"

    def _btc_momentum(self, lookback_s: float) -> float:
        now_ts = time.time()
        pts = [x for x in self.btc_spot_history if (now_ts - x[0]) <= lookback_s]
        if len(pts) < 2:
            return 0.0
        p0, p1 = pts[0][1], pts[-1][1]
        if p0 <= 0:
            return 0.0
        return (p1 - p0) / p0

    def try_gpt_mode(self, books: TopOfBook, runtime_stats: RuntimeStats):
        if not self._can_open_new_buy():
            self._record_skip("gpt:max_trades")
            return
        if books.up_ask is None or books.dn_ask is None or books.up_bid is None or books.dn_bid is None:
            self._record_skip("gpt:missing_book")
            return

        self._fetch_btc_spot(force=self.collect_mode)
        mom15 = self._btc_momentum(15.0)
        mom60 = self._btc_momentum(60.0)

        up_mid = (books.up_bid + books.up_ask) / 2.0
        dn_mid = (books.dn_bid + books.dn_ask) / 2.0
        denom = max(1e-9, up_mid + dn_mid)
        implied_up = clamp(up_mid / denom, 0.0, 1.0)

        up_imb = ((books.up_bid_sz or 0.0) - (books.up_ask_sz or 0.0)) / max(1e-9, (books.up_bid_sz or 0.0) + (books.up_ask_sz or 0.0))
        dn_imb = ((books.dn_bid_sz or 0.0) - (books.dn_ask_sz or 0.0)) / max(1e-9, (books.dn_bid_sz or 0.0) + (books.dn_ask_sz or 0.0))

        directional = clamp((mom15 * 120.0) + (mom60 * 70.0), -1.0, 1.0)
        meanrev = clamp((0.5 - implied_up) * 2.0, -1.0, 1.0)
        book_edge = clamp((up_imb - dn_imb) * 0.5, -1.0, 1.0)

        up_score = 0.55 * directional + 0.30 * book_edge + 0.15 * meanrev
        dn_score = -0.55 * directional - 0.30 * book_edge - 0.15 * meanrev

        side = "UP" if up_score > dn_score else "DOWN"
        raw_signal = up_score if side == "UP" else dn_score
        signal = clamp(abs(raw_signal), 0.0, 1.0)
        self.gpt_last_signal = f"side={side} signal={signal:.3f} mom15={mom15:.4%} mom60={mom60:.4%} implied_up={implied_up:.3f}"

        if signal < self.gpt_min_signal:
            self._record_skip("gpt:signal_too_weak")
            return

        ask = books.up_ask if side == "UP" else books.dn_ask
        ask_sz = (books.up_ask_sz or 0.0) if side == "UP" else (books.dn_ask_sz or 0.0)
        token = self.meta.token_ids[0] if side == "UP" else self.meta.token_ids[1]
        if ask is None or ask_sz <= 0:
            self._record_skip("gpt:no_liquidity")
            return
        spread = ((books.up_ask - books.up_bid) if side == "UP" else (books.dn_ask - books.dn_bid))
        if spread > 0.02:
            self._record_skip("gpt:spread_too_wide")
            return

        budget = self.remaining_budget()
        alloc_usd = budget * self.gpt_alloc_fraction * (0.35 + 0.65 * signal)
        qty = min(self.step_shares, ask_sz, self.remaining_session_shares(), alloc_usd / max(1e-9, self.est_effective_cost(ask)))
        if qty <= 0 or not self._meets_min_order(ask, qty):
            self._record_skip("gpt:qty_too_small")
            return

        delta_up, delta_dn = (qty, 0.0) if side == "UP" else (0.0, qty)
        added_paid = self.est_effective_cost(ask * qty)
        if not self._can_buy_with_loss_limit(delta_up, delta_dn, added_paid, self.hedge_minor_loss_limit):
            self._record_skip("gpt:settlement_guard")
            return

        ok, err = self._post_buy(token, ask, qty, f"gpt mode buy {side} sig={signal:.3f}")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "BUY", side, qty, ask, self._buy_note(f"gpt mode buy {side} sig={signal:.3f}", ask, ask), ok, err))
        if ok:
            self._record_purchase(token, ask, qty)
            self.spent_est += added_paid

    def try_fortress_mode(self, books: TopOfBook, pos: PositionSnapshot, runtime_stats: RuntimeStats):
        if not self._can_open_new_buy():
            self._record_skip("fortress:max_trades")
            return
        if books.up_ask is None or books.dn_ask is None:
            self._record_skip("fortress:missing_ask")
            return

        budget = self.remaining_budget()
        if budget <= 0:
            self._record_skip("fortress:no_budget")
            return

        # Core pair lock: only buy both sides when fees-inclusive bundle has positive lock edge.
        pair_cost = self.est_effective_cost(books.up_ask + books.dn_ask)
        lock_edge = 1.0 - pair_cost
        if lock_edge >= self.fortress_lock_edge:
            max_by_book = min(books.up_ask_sz or 0.0, books.dn_ask_sz or 0.0)
            max_by_budget = budget / max(1e-9, pair_cost)
            qty = min(self.step_shares, self.remaining_session_shares(), max_by_book, max_by_budget)
            if qty > 0 and self._meets_min_order((books.up_ask + books.dn_ask) / 2.0, qty):
                added_paid = self.est_effective_cost((books.up_ask + books.dn_ask) * qty)
                if self._can_buy_with_loss_limit(qty, qty, added_paid, self.fortress_loss_cap):
                    ok1, err1 = self._post_buy(self.meta.token_ids[0], books.up_ask, qty, "fortress pair lock")
                    ok2, err2 = self._post_buy(self.meta.token_ids[1], books.dn_ask, qty, "fortress pair lock")
                    ts = now_utc().astimezone().strftime("%H:%M:%S")
                    self.log_action(TradeAction(ts, "BUY", "UP", qty, books.up_ask, self._buy_note("fortress pair lock", books.up_ask, books.up_ask), ok1, err1))
                    self.log_action(TradeAction(ts, "BUY", "DOWN", qty, books.dn_ask, self._buy_note("fortress pair lock", books.dn_ask, books.dn_ask), ok2, err2))
                    if ok1:
                        self._record_purchase(self.meta.token_ids[0], books.up_ask, qty)
                        self.spent_est += self.est_effective_cost(books.up_ask * qty)
                    if ok2:
                        self._record_purchase(self.meta.token_ids[1], books.dn_ask, qty)
                        self.spent_est += self.est_effective_cost(books.dn_ask * qty)
                    return

        # If no lock edge, do bounded directional tilt only when cushion exists.
        worst = min(runtime_stats.pnl_if_up_wins, runtime_stats.pnl_if_down_wins)
        cushion = worst + self.fortress_loss_cap
        if cushion <= 0:
            self._record_skip("fortress:no_cushion")
            return
        net_imb = self._net_imbalance(pos)
        if abs(net_imb) >= self.fortress_max_imbalance:
            self._record_skip("fortress:imbalance_cap")
            return

        self._fetch_btc_spot(force=self.collect_mode)
        mom15 = self._btc_momentum(15.0)
        mom60 = self._btc_momentum(60.0)
        directional = clamp((mom15 * 120.0) + (mom60 * 70.0), -1.0, 1.0)
        if abs(directional) < 0.12:
            self._record_skip("fortress:signal_weak")
            return

        side = "UP" if directional > 0 else "DOWN"
        ask = books.up_ask if side == "UP" else books.dn_ask
        ask_sz = (books.up_ask_sz or 0.0) if side == "UP" else (books.dn_ask_sz or 0.0)
        token = self.meta.token_ids[0] if side == "UP" else self.meta.token_ids[1]
        if ask is None or ask_sz <= 0:
            self._record_skip("fortress:no_liquidity")
            return

        alloc_usd = cushion * self.fortress_tilt_budget
        qty = min(self.fortress_max_tilt_shares, self.step_shares, self.remaining_session_shares(), ask_sz, alloc_usd / max(1e-9, self.est_effective_cost(ask)), budget / max(1e-9, self.est_effective_cost(ask)))
        if qty <= 0 or not self._meets_min_order(ask, qty):
            self._record_skip("fortress:qty_small")
            return
        d_up, d_dn = (qty, 0.0) if side == "UP" else (0.0, qty)
        added_paid = self.est_effective_cost(ask * qty)
        if not self._can_buy_with_loss_limit(d_up, d_dn, added_paid, self.fortress_loss_cap):
            self._record_skip("fortress:loss_guard")
            return

        ok, err = self._post_buy(token, ask, qty, f"fortress tilt {side} sig={directional:.3f}")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "BUY", side, qty, ask, self._buy_note(f"fortress tilt {side} sig={directional:.3f}", ask, ask), ok, err))
        if ok:
            self._record_purchase(token, ask, qty)
            self.spent_est += self.est_effective_cost(ask * qty)

    def _update_flip_history(self, books: TopOfBook):
        now_ts = time.time()
        if books.up_bid is not None and books.up_ask is not None:
            self.flip_history["UP"].append((now_ts, (books.up_bid + books.up_ask) / 2.0, books.up_bid, books.up_ask))
        if books.dn_bid is not None and books.dn_ask is not None:
            self.flip_history["DOWN"].append((now_ts, (books.dn_bid + books.dn_ask) / 2.0, books.dn_bid, books.dn_ask))

    def _flip_signal(self, side: str, books: TopOfBook) -> Tuple[bool, str, float]:
        now_ts = time.time()
        data = [x for x in self.flip_history[side] if (now_ts - x[0]) <= self.flip_signal_window_s]
        if len(data) < self.flip_min_samples:
            return False, "warming_up", 0.0

        bid = books.up_bid if side == "UP" else books.dn_bid
        ask = books.up_ask if side == "UP" else books.dn_ask
        if bid is None or ask is None:
            return False, "no_book", 0.0

        mids = [x[1] for x in data]
        returns = [mids[i] - mids[i - 1] for i in range(1, len(mids))]
        if not returns:
            return False, "no_returns", 0.0

        rng = max(mids) - min(mids)
        spread = max(0.0, ask - bid)
        avg_abs_ret = sum(abs(x) for x in returns) / len(returns)
        drift = mids[-1] - mids[0]
        recent_trend = mids[-1] - mids[max(0, len(mids) - 5)]
        mid_now = (bid + ask) / 2.0
        rebound = mid_now - min(mids)

        # Oscillation detector: how often micro-momentum flips in the sampling window.
        move_thresh = max(self.meta.tick_size * 0.5, 0.003)
        flip_count = 0
        prev_sign = 0
        for d in returns:
            sign = 1 if d > move_thresh else (-1 if d < -move_thresh else 0)
            if sign != 0 and prev_sign != 0 and sign != prev_sign:
                flip_count += 1
            if sign != 0:
                prev_sign = sign

        # Mean-reversion entry: buy near the lower part of local range.
        pos_in_range = 0.5
        if rng > 1e-9:
            pos_in_range = (ask - min(mids)) / rng

        # Short-horizon bounce: last move should be turning upward from recent weakness.
        last_ret = returns[-1]
        recent_bias = sum(returns[-4:-1]) if len(returns) >= 4 else sum(returns[:-1])

        score = 0.0
        if rng >= max(0.015, self.meta.tick_size * 3):
            score += 1.0
        if avg_abs_ret >= max(0.0025, self.meta.tick_size * 0.45):
            score += 1.0
        if flip_count >= 4:
            score += 1.0
        if pos_in_range <= 0.35:
            score += 1.0
        if last_ret > 0 and recent_bias < 0:
            score += 1.0

        if spread > 0.02:
            return False, f"wide_spread:{spread:.3f}", score
        if mid_now < self.flip_entry_price_min or mid_now > self.flip_entry_price_max:
            return False, f"price_band:{mid_now:.3f}", score
        if abs(drift) > self.flip_max_window_drift or abs(recent_trend) > (self.flip_max_window_drift * 0.8):
            return False, f"trend_too_strong:d={drift:.3f}", score
        if rebound < self.flip_min_rebound_cents:
            return False, f"no_rebound:{rebound:.3f}", score
        if score < 3.5:
            return False, f"weak_score:{score:.1f}", score
        return True, f"score:{score:.1f} flips:{flip_count} rng:{rng:.3f} pos:{pos_in_range:.2f} d:{drift:.3f}", score

    def _try_open_flip_position(self, side: str, books: TopOfBook):
        if side in self.flip_open:
            return
        if not self._can_open_new_buy():
            self._record_skip("flip:max_trades")
            return
        if (time.time() - self.flip_last_exit_ts.get(side, 0.0)) < self.flip_cooldown_s:
            self._record_skip("flip:cooldown")
            return
        signal_ok, signal_note, signal_score = self._flip_signal(side, books)
        self.flip_signal_debug[side] = signal_note
        if not signal_ok:
            self._record_skip(f"flip:signal:{signal_note.split(':')[0]}")
            return
        if self.remaining_session_shares() <= 0:
            self._record_skip("flip:session_cap")
            return
        if side == "UP":
            ask = books.up_ask
            bid = books.up_bid
            ask_sz = books.up_ask_sz or 0.0
            token = self.meta.token_ids[0]
        else:
            ask = books.dn_ask
            bid = books.dn_bid
            ask_sz = books.dn_ask_sz or 0.0
            token = self.meta.token_ids[1]
        if ask is None or bid is None or ask_sz <= 0:
            return
        if ask < self.flip_entry_price_min or ask > self.flip_entry_price_max:
            self._record_skip("flip:price_band")
            return
        spread = max(0.0, ask - bid)
        if spread > self.flip_max_spread:
            self._record_skip("flip:spread_too_wide")
            self.flip_signal_debug[side] = f"wide_spread:{spread:.3f}"
            return

        planned_exit = ask + self.flip_target_cents
        exp_edge = (planned_exit * (1.0 - self.meta.taker_fee_rate)) - (ask * (1.0 + self.meta.taker_fee_rate))
        if exp_edge < self.flip_min_expected_edge:
            self._record_skip("flip:expected_edge_too_low")
            self.flip_signal_debug[side] = f"edge_low:{exp_edge:.4f}"
            return

        budget = self.remaining_budget()
        qty = min(self.step_shares, ask_sz, budget / self.est_effective_cost(ask))
        qty = self._limit_buy_qty_by_session(qty)
        if qty <= 0 or (not self._meets_min_order(ask, qty)):
            self._record_skip("flip:min_order_or_budget")
            return
        ok, err = self._post_buy(token, ask, qty, f"flip scalp entry {side} ({signal_note})")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "BUY", side, qty, ask, self._buy_note(f"flip scalp entry {side} ({signal_note})", ask, ask), ok, err))
        if ok:
            self._record_purchase(token, ask, qty)
            self.spent_est += self.est_effective_cost(ask * qty)
            self.flip_open[side] = {
                "qty": qty,
                "entry": ask,
                "target": ask + self.flip_target_cents,
                "token": token,
                "score": signal_score,
                "entry_ts": time.time(),
                "high_bid": bid,
            }

    def _should_hold_flip_for_settlement(self, side: str, qty: float, pos: PositionSnapshot) -> bool:
        if not self.flip_hold_hedged_pairs:
            return False
        if qty <= 0:
            return False
        hedged_qty = min(pos.up.size, pos.down.size)
        if hedged_qty + 1e-9 < qty:
            return False
        if side == "UP" and pos.up.size > self.max_side_position_shares:
            return False
        if side == "DOWN" and pos.down.size > self.max_side_position_shares:
            return False
        pair_cost = pos.up.avg_price + pos.down.avg_price
        return pair_cost <= (1.0 - self.flip_hold_min_edge)

    def _flip_sellable_qty(self, side: str, pos: PositionSnapshot) -> float:
        reserve = max(0.0, self.flip_hedge_reserve_qty)
        if side == "UP":
            return max(0.0, pos.up.size - reserve)
        return max(0.0, pos.down.size - reserve)

    def _try_close_flip_position(self, side: str, books: TopOfBook, pos: PositionSnapshot):
        open_pos = self.flip_open.get(side)
        if not open_pos:
            return
        if side == "UP":
            bid = books.up_bid
            ask = books.up_ask
            bid_sz = books.up_bid_sz or 0.0
        else:
            bid = books.dn_bid
            ask = books.dn_ask
            bid_sz = books.dn_bid_sz or 0.0
        if bid is None or bid_sz <= 0:
            return
        now_ts = time.time()
        if now_ts < self.flip_next_exit_retry_ts.get(side, 0.0):
            self._record_skip("flip:exit_retry_wait")
            return
        target_qty = float(open_pos["qty"])
        qty = min(target_qty, bid_sz)
        if self._should_hold_flip_for_settlement(side, qty, pos):
            self.logger.info(
                "Flip hold-for-settlement active: side=%s qty=%.4f hedged_qty=%.4f pair_cost=%.4f",
                side,
                qty,
                min(pos.up.size, pos.down.size),
                (pos.up.avg_price + pos.down.avg_price),
            )
            self.flip_hedge_reserve_qty = max(self.flip_hedge_reserve_qty, qty)
            self.flip_open.pop(side, None)
            self.flip_exit_fail_count[side] = 0
            self.flip_next_exit_retry_ts[side] = 0.0
            self._record_skip("flip:hold_for_settlement")
            return
        sellable_qty = self._flip_sellable_qty(side, pos)
        qty = min(qty, sellable_qty)
        if qty <= 0:
            self.flip_open.pop(side, None)
            self._record_skip("flip:reserve_protected")
            return
        target = float(open_pos["target"])
        entry = float(open_pos["entry"])
        stop_price = entry - self.flip_stop_loss_cents
        entry_ts = float(open_pos.get("entry_ts", time.time()))
        open_pos["high_bid"] = max(float(open_pos.get("high_bid", bid)), bid)
        high_bid = float(open_pos.get("high_bid", bid))
        armed_trail = high_bid >= (entry + self.flip_trail_arm_cents)
        trail_stop = high_bid - self.flip_trail_gap_cents
        hold_s = max(0.0, time.time() - entry_ts)
        exit_reason = ""
        if armed_trail and bid <= trail_stop and bid > entry:
            exit_reason = "trail_take"
        elif bid >= target:
            exit_reason = "target"
        elif bid <= stop_price:
            exit_reason = "stop_loss"
        elif hold_s >= self.flip_max_hold_s and bid >= entry:
            exit_reason = "time_exit"
        else:
            return
        sell_px = self._sell_limit_price(bid, ask)
        if sell_px is None:
            self._record_skip("flip:no_sell_price")
            return
        ok, err = self._post_sell(str(open_pos["token"]), sell_px, qty, f"flip scalp exit {side} ({exit_reason})")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "SELL", side, qty, sell_px, f"flip scalp exit {side} ({exit_reason})", ok, err))
        if not ok:
            low = (err or "").lower()
            if "not enough balance" in low or "allowance" in low:
                self.flip_exit_fail_count[side] = self.flip_exit_fail_count.get(side, 0) + 1
                backoff_s = min(12.0, 1.5 * self.flip_exit_fail_count[side])
                self.flip_next_exit_retry_ts[side] = time.time() + backoff_s
                self.logger.warning(
                    "Flip exit deferred (%s) due to balance/allowance; retry in %.1fs (fail_count=%s).",
                    side,
                    backoff_s,
                    self.flip_exit_fail_count[side],
                )
                self.refresh_wallet_debug(force=True)
            return
        self.flip_exit_fail_count[side] = 0
        self.flip_next_exit_retry_ts[side] = 0.0
        credit = max(0.0, bid * qty * (1.0 - self.meta.taker_fee_rate))
        self.spent_est = max(0.0, self.spent_est - credit)
        self.flip_open.pop(side, None)
        self.flip_last_exit_ts[side] = time.time()
        if exit_reason == "stop_loss":
            self.flip_stoploss_streak += 1
            if self.flip_stoploss_streak >= self.flip_stoploss_streak_limit:
                self.flip_pause_until_ts = time.time() + self.flip_pause_after_stops_s
                self.logger.warning(
                    "Flip scalp pause armed after stop-loss streak=%s; pause_s=%.1f",
                    self.flip_stoploss_streak,
                    self.flip_pause_after_stops_s,
                )
        else:
            self.flip_stoploss_streak = 0

    def try_flip_scalp(self, books: TopOfBook, pos: PositionSnapshot):
        if self.disable_flip_scalp:
            return
        if time.time() < self.flip_pause_until_ts:
            self._record_skip("flip:paused_after_losses")
            return
        self._update_flip_history(books)
        self._try_close_flip_position("UP", books, pos)
        self._try_close_flip_position("DOWN", books, pos)
        self._try_open_flip_position("UP", books)
        self._try_open_flip_position("DOWN", books)

    def _upswing_signal(self, side: str, books: TopOfBook) -> Tuple[bool, str, float, Dict[str, float]]:
        now_ts = time.time()
        data = [x for x in self.flip_history[side] if (now_ts - x[0]) <= self.upswing_window_s]
        if len(data) < self.upswing_min_samples:
            return False, "warming_up", 0.0, {}

        bid = books.up_bid if side == "UP" else books.dn_bid
        ask = books.up_ask if side == "UP" else books.dn_ask
        bid_sz = (books.up_bid_sz or 0.0) if side == "UP" else (books.dn_bid_sz or 0.0)
        ask_sz = (books.up_ask_sz or 0.0) if side == "UP" else (books.dn_ask_sz or 0.0)
        if bid is None or ask is None:
            return False, "no_book", 0.0, {}

        mids = [x[1] for x in data]
        rets = [mids[i] - mids[i - 1] for i in range(1, len(mids))]
        if len(rets) < 4:
            return False, "no_returns", 0.0, {}

        # EMA trend structure
        alpha_fast = 2.0 / (4.0 + 1.0)
        alpha_slow = 2.0 / (10.0 + 1.0)
        ema_fast = mids[0]
        ema_slow = mids[0]
        for x in mids[1:]:
            ema_fast = alpha_fast * x + (1 - alpha_fast) * ema_fast
            ema_slow = alpha_slow * x + (1 - alpha_slow) * ema_slow

        drift = mids[-1] - mids[0]
        recent = mids[-1] - mids[max(0, len(mids) - 4)]
        rng = max(mids) - min(mids)
        pos = 0.5
        if rng > 1e-9:
            pos = clamp((mids[-1] - min(mids)) / rng, 0.0, 1.0)

        accel = (rets[-1] + rets[-2]) - (rets[0] + rets[1])
        pos_ratio = sum(1 for r in rets if r > 0) / max(1, len(rets))
        vol = sum(abs(r) for r in rets) / max(1, len(rets))
        spread = max(0.0, ask - bid)
        imbalance = (bid_sz - ask_sz) / max(1e-9, (bid_sz + ask_sz))

        # BTC confirmation for macro direction (UP should prefer positive BTC momo, DOWN negative)
        btc_momo = self._btc_momentum(20.0)
        btc_dir_ok = (btc_momo >= 0) if side == "UP" else (btc_momo <= 0)

        score = 0.0
        if ema_fast > ema_slow:
            score += 1.2
        if drift >= self.upswing_min_momentum_cents:
            score += 1.1
        if recent >= self.upswing_min_momentum_cents * 0.55:
            score += 0.8
        if accel > 0:
            score += 0.6
        if pos_ratio >= 0.62:
            score += 0.6
        if pos >= 0.60:
            score += 0.6
        if imbalance > -0.15:
            score += 0.4
        if btc_dir_ok:
            score += 0.4

        if spread > max(self.flip_max_spread, 0.015):
            return False, f"wide_spread:{spread:.3f}", score, {"vol": vol, "spread": spread, "drift": drift, "recent": recent}
        if score < self.upswing_min_score:
            return False, f"weak_score:{score:.2f}", score, {"vol": vol, "spread": spread, "drift": drift, "recent": recent}

        note = f"score:{score:.2f} drift:{drift:.3f} rec:{recent:.3f} vol:{vol:.3f} pos:{pos:.2f}"
        return True, note, score, {"vol": vol, "spread": spread, "drift": drift, "recent": recent}

    def _try_open_upswing_position(self, side: str, books: TopOfBook):
        if side in self.upswing_open:
            return
        if self.upswing_open:
            self._record_skip("upswing:single_position_guard")
            return
        if not self._can_open_new_buy():
            self._record_skip("upswing:max_trades")
            return
        if self.remaining_session_shares() <= 0:
            self._record_skip("upswing:session_cap")
            return
        if (time.time() - self.upswing_last_exit_ts.get(side, 0.0)) < self.upswing_cooldown_s:
            self._record_skip("upswing:cooldown")
            return

        signal_ok, signal_note, score, feat = self._upswing_signal(side, books)
        self.upswing_signal_debug[side] = signal_note
        if not signal_ok:
            self._record_skip(f"upswing:signal:{signal_note.split(':')[0]}")
            return

        if side == "UP":
            ask = books.up_ask
            ask_sz = books.up_ask_sz or 0.0
            token = self.meta.token_ids[0]
        else:
            ask = books.dn_ask
            ask_sz = books.dn_ask_sz or 0.0
            token = self.meta.token_ids[1]
        if ask is None or ask_sz <= 0:
            return

        vol = float(feat.get("vol", self.upswing_take_profit_cents))
        dynamic_tp = max(self.upswing_take_profit_cents, vol * 1.35)
        dynamic_sl = max(self.upswing_stop_loss_cents, vol * 0.95)
        exp_edge = (ask + dynamic_tp) * (1.0 - self.meta.taker_fee_rate) - (ask * (1.0 + self.meta.taker_fee_rate))
        if exp_edge <= max(0.001, self.flip_min_expected_edge * 0.5):
            self._record_skip("upswing:expected_edge_low")
            return

        budget = self.remaining_budget()
        score_mult = clamp((score - self.upswing_min_score) / 2.0, 0.2, 1.0)
        qty = min(self.step_shares * score_mult, ask_sz, budget / max(1e-9, self.est_effective_cost(ask)))
        qty = self._limit_buy_qty_by_session(qty)
        if qty <= 0 or (not self._meets_min_order(ask, qty)):
            self._record_skip("upswing:min_order_or_budget")
            return

        ok, err = self._post_buy(token, ask, qty, f"upswing entry {side} ({signal_note})")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "BUY", side, qty, ask, self._buy_note(f"upswing entry {side} ({signal_note})", ask, ask), ok, err))
        if ok:
            self._record_purchase(token, ask, qty)
            self.spent_est += self.est_effective_cost(ask * qty)
            self.upswing_open[side] = {
                "qty": qty,
                "entry": ask,
                "target": ask + dynamic_tp,
                "stop": max(0.0, ask - dynamic_sl),
                "token": token,
                "score": score,
                "entry_ts": time.time(),
                "high_bid": ask,
            }

    def _try_close_upswing_position(self, side: str, books: TopOfBook):
        open_pos = self.upswing_open.get(side)
        if not open_pos:
            return
        if side == "UP":
            bid = books.up_bid
            ask = books.up_ask
            bid_sz = books.up_bid_sz or 0.0
        else:
            bid = books.dn_bid
            ask = books.dn_ask
            bid_sz = books.dn_bid_sz or 0.0
        if bid is None or bid_sz <= 0:
            return

        qty = min(float(open_pos["qty"]), bid_sz)
        if qty <= 0:
            return

        target = float(open_pos["target"])
        stop = float(open_pos["stop"])
        entry = float(open_pos["entry"])
        high_bid = max(float(open_pos.get("high_bid", bid)), bid)
        open_pos["high_bid"] = high_bid
        trail_stop = high_bid - self.upswing_trail_gap_cents
        hold_s = max(0.0, time.time() - float(open_pos.get("entry_ts", time.time())))
        _, rev_note, rev_score, _ = self._upswing_signal(side, books)

        exit_reason = ""
        if bid >= target:
            exit_reason = "take_profit"
        elif bid <= stop:
            exit_reason = "stop_limit"
        elif high_bid > entry and bid <= trail_stop:
            exit_reason = "trail_stop"
        elif rev_score < (self.upswing_min_score - 0.7) and hold_s > 3.0:
            exit_reason = f"signal_reversal:{rev_note}"
        elif hold_s >= self.upswing_max_hold_s and bid >= entry:
            exit_reason = "time_exit"
        else:
            return

        sell_px = self._sell_limit_price(bid, ask)
        if sell_px is None:
            self._record_skip("upswing:no_sell_price")
            return
        ok, err = self._post_sell(str(open_pos["token"]), sell_px, qty, f"upswing exit {side} ({exit_reason})")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "SELL", side, qty, sell_px, f"upswing exit {side} ({exit_reason})", ok, err))
        if not ok:
            self._record_skip("upswing:sell_failed")
            return

        credit = max(0.0, bid * qty * (1.0 - self.meta.taker_fee_rate))
        self.spent_est = max(0.0, self.spent_est - credit)
        self.upswing_open.pop(side, None)
        self.upswing_last_exit_ts[side] = time.time()

    def try_upswing_scalp(self, books: TopOfBook, pos: PositionSnapshot):
        self._update_flip_history(books)
        self._try_close_upswing_position("UP", books)
        self._try_close_upswing_position("DOWN", books)
        if self._has_risky_imbalance(pos):
            self._record_skip("upswing:risky_imbalance")
            return

        up_ok, up_note, up_score, _ = self._upswing_signal("UP", books)
        dn_ok, dn_note, dn_score, _ = self._upswing_signal("DOWN", books)
        self.upswing_signal_debug["UP"] = up_note
        self.upswing_signal_debug["DOWN"] = dn_note

        if up_ok and (not dn_ok or up_score >= dn_score):
            self._try_open_upswing_position("UP", books)
        elif dn_ok:
            self._try_open_upswing_position("DOWN", books)

    def _ml_strategy_params(self, idx: int) -> Dict[str, float]:
        presets = [
            {"btc_w": 0.80, "book_w": 0.35, "micro_w": 0.30, "thr": 0.26, "pair_edge": 0.012, "alloc": 0.22},
            {"btc_w": 0.55, "book_w": 0.70, "micro_w": 0.25, "thr": 0.22, "pair_edge": 0.010, "alloc": 0.18},
            {"btc_w": 0.30, "book_w": 0.40, "micro_w": 0.75, "thr": 0.28, "pair_edge": 0.014, "alloc": 0.25},
            {"btc_w": 0.70, "book_w": 0.25, "micro_w": 0.55, "thr": 0.24, "pair_edge": 0.011, "alloc": 0.20},
        ]
        return presets[idx % len(presets)]

    def _ml_pick_strategy(self) -> int:
        n = len(self.ml_scores)
        now_ts = time.time()
        if now_ts - self.ml_last_switch_ts < 4.0:
            return self.ml_active_idx
        self.ml_last_switch_ts = now_ts
        import random
        if random.random() < self.ml_explore_rate:
            return random.randrange(n)
        best_i = 0
        best_v = -1e18
        for i in range(n):
            denom = max(1, self.ml_trials[i])
            v = self.ml_scores[i] / denom
            if v > best_v:
                best_v = v
                best_i = i
        return best_i

    def _ml_signal(self, books: TopOfBook, idx: int) -> Tuple[float, str]:
        if books.up_bid is None or books.up_ask is None or books.dn_bid is None or books.dn_ask is None:
            return 0.0, "no_book"
        p = self._ml_strategy_params(idx)
        self._fetch_btc_spot(force=self.collect_mode)
        b15 = self._btc_momentum(15.0)
        b45 = self._btc_momentum(45.0)
        btc_sig = clamp((b15 * 180.0) + (b45 * 120.0), -1.0, 1.0)

        up_mid = (books.up_bid + books.up_ask) / 2.0
        dn_mid = (books.dn_bid + books.dn_ask) / 2.0
        denom = max(1e-9, up_mid + dn_mid)
        book_sig = clamp((up_mid / denom) - 0.5, -0.5, 0.5) * 2.0

        self._update_flip_history(books)
        micro_up = self._micro_trend("UP")
        micro_dn = self._micro_trend("DOWN")
        micro_sig = clamp((micro_up - micro_dn) * 8.0, -1.0, 1.0)

        sig = (p["btc_w"] * btc_sig) + (p["book_w"] * book_sig) + (p["micro_w"] * micro_sig)
        sig = clamp(sig / max(1e-9, (p["btc_w"] + p["book_w"] + p["micro_w"])), -1.0, 1.0)
        return sig, f"s={sig:.3f} btc={btc_sig:.3f} book={book_sig:.3f} micro={micro_sig:.3f}"

    def _ml_equity_mark(self, books: TopOfBook) -> float:
        eq = self.ml_virtual_cash
        if books.up_bid is not None and self.ml_up_qty > 0:
            eq += max(0.0, books.up_bid * self.ml_up_qty * (1.0 - self.meta.taker_fee_rate))
        if books.dn_bid is not None and self.ml_dn_qty > 0:
            eq += max(0.0, books.dn_bid * self.ml_dn_qty * (1.0 - self.meta.taker_fee_rate))
        return eq

    def _ml_record_buy(self, side: str, qty: float, px: float, note: str):
        cost = self.est_effective_cost(px * qty)
        if cost <= 0 or cost > self.ml_virtual_cash:
            return False
        self.ml_virtual_cash -= cost
        if side == "UP":
            self.ml_up_qty += qty
            self.ml_up_cost += cost
        else:
            self.ml_dn_qty += qty
            self.ml_dn_cost += cost
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "BUY", side, qty, px, note, True, ""))
        return True

    def try_ml_mode(self, books: TopOfBook, pos: PositionSnapshot):
        if books.up_bid is None or books.up_ask is None or books.dn_bid is None or books.dn_ask is None:
            self._record_skip("ml:no_book")
            return

        idx = self._ml_pick_strategy()
        sig, note = self._ml_signal(books, idx)
        p = self._ml_strategy_params(idx)
        self.ml_active_idx = idx
        self.ml_last_signal = note

        # Reward currently active strategy by incremental marked-equity gain.
        eq_now = self._ml_equity_mark(books)
        pnl_delta = eq_now - self.ml_last_equity
        self.ml_scores[idx] += pnl_delta
        self.ml_trials[idx] += 1
        self.ml_last_equity = eq_now

        # Buy-only market-neutral pair-lock first (inspired by buy-only wallet behavior).
        pair_edge = max(self.ml_pair_lock_edge, p["pair_edge"])
        pair_cost = books.up_ask + books.dn_ask
        if pair_cost <= (1.0 - pair_edge):
            qty_cap_cash = self.ml_virtual_cash / max(1e-9, self.est_effective_cost(pair_cost))
            qty = min(self.step_shares, books.up_ask_sz or 0.0, books.dn_ask_sz or 0.0, qty_cap_cash)
            if qty > 0 and self._meets_min_order(books.up_ask, qty) and self._meets_min_order(books.dn_ask, qty):
                up_ok = self._ml_record_buy("UP", qty, books.up_ask, f"ml buy-only pair-lock strat={idx} edge={1.0-pair_cost:.4f} {note}")
                dn_ok = self._ml_record_buy("DOWN", qty, books.dn_ask, f"ml buy-only pair-lock strat={idx} edge={1.0-pair_cost:.4f} {note}")
                if up_ok and dn_ok:
                    return

        # Optional directional overlay buys only when still balanced and signal is strong.
        if abs(self.ml_up_qty - self.ml_dn_qty) >= self.ml_max_imbalance_shares:
            self._record_skip("ml:imbalance_cap")
            return
        if abs(sig) < p["thr"]:
            self._record_skip("ml:signal_weak")
            return

        side = "UP" if sig > 0 else "DOWN"
        ask = books.up_ask if side == "UP" else books.dn_ask
        ask_sz = (books.up_ask_sz or 0.0) if side == "UP" else (books.dn_ask_sz or 0.0)
        if ask is None or ask_sz <= 0:
            self._record_skip("ml:no_liquidity")
            return
        if ask < self.flip_entry_price_min or ask > self.flip_entry_price_max:
            self._record_skip("ml:price_band")
            return

        alloc = self.ml_virtual_cash * clamp(p["alloc"] + abs(sig) * 0.10, 0.08, 0.35)
        qty = min(self.step_shares, ask_sz, alloc / max(1e-9, self.est_effective_cost(ask)))
        if qty <= 0 or not self._meets_min_order(ask, qty):
            self._record_skip("ml:qty_small")
            return

        if not self._ml_record_buy(side, qty, ask, f"ml buy-only tilt strat={idx} {note}"):
            self._record_skip("ml:cash_limit")

    def _collect_market_sample(self, books: TopOfBook):
        if not self.collect_mode or not self.collect_data_csv:
            return
        now_ts = time.time()
        if now_ts - self._collect_last_ts < max(0.05, self.poll_s * 0.9):
            return
        self._collect_last_ts = now_ts
        try:
            pth = Path(self.collect_data_csv)
            if pth.parent and str(pth.parent) != ".":
                pth.parent.mkdir(parents=True, exist_ok=True)
            exists = pth.exists()
            t_now = now_utc()
            row = {
                "ts_utc": t_now.isoformat(),
                "market_name": self.meta.question,
                "slug": self.meta.slug,
                "market_start_utc": "" if not self.meta.start_dt_utc else self.meta.start_dt_utc.isoformat(),
                "market_end_utc": "" if not self.meta.end_dt_utc else self.meta.end_dt_utc.isoformat(),
                "tte_s": self.time_to_end_s(),
                "up_bid": books.up_bid,
                "up_ask": books.up_ask,
                "up_bid_sz": books.up_bid_sz,
                "up_ask_sz": books.up_ask_sz,
                "down_bid": books.dn_bid,
                "down_ask": books.dn_ask,
                "down_bid_sz": books.dn_bid_sz,
                "down_ask_sz": books.dn_ask_sz,
                "btc_spot_usd": self._last_btc_price,
                "btc_open_usd": self.btc_market_open_price,
                "btc_source": self.btc_price_source,
                "btc_open_source": self.btc_market_open_source,
                "chainlink_last_updated_at": self.chainlink_last_updated_at,
                "chainlink_age_s": (None if not self.chainlink_last_updated_at else max(0.0, now_ts - float(self.chainlink_last_updated_at))),
                "btc_low_latency_mode": self.btc_low_latency_mode,
                "btc_fast_probe_timeout_s": self.btc_fast_probe_timeout_s,
                "btc_ws_source": self.btc_price_source,
                "btc_ws_last_update_ts": self.btc_ws_last_update_ts,
                "btc_ws_age_s": (None if self.btc_ws_last_update_ts <= 0 else max(0.0, now_ts - self.btc_ws_last_update_ts)),
                "price_feed_mode": self.price_feed_mode,
                "ws_last_update_ts": self.ws_last_update_ts,
            }
            cols = list(row.keys())
            with pth.open("a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=cols)
                if not exists:
                    w.writeheader()
                w.writerow(row)
            self.collect_samples_count += 1
        except Exception:
            self.logger.exception("collect_market_sample_failed")

    def _replication_dynamic_min_edge(self, tte: Optional[int]) -> float:
        dyn = self.replication_min_set_edge
        if tte is None:
            return dyn
        if self.successful_buy_trades <= 0 and tte <= min(self.replication_window_s, 120.0):
            dyn = min(dyn, -0.006)
        elif tte <= 35:
            dyn = min(dyn, -0.004)
        return dyn

    def _write_replication_diag(self, books: TopOfBook, pos: PositionSnapshot, tte: Optional[int], status_bits: List[str]):
        if (not self.replication_mode) or (not self.replication_diag_log):
            return
        now_ts = time.time()
        if now_ts - self._replication_diag_last_ts < 0.4:
            return
        self._replication_diag_last_ts = now_ts
        try:
            pth = Path(self.replication_diag_log)
            if pth.parent and str(pth.parent) != ".":
                pth.parent.mkdir(parents=True, exist_ok=True)
            rec = {
                "ts_utc": now_utc().isoformat(),
                "slug": self.meta.slug,
                "mode": "replication",
                "live": self.live,
                "tte": tte,
                "window_s": self.replication_window_s,
                "cadence_s": self.replication_cadence_s,
                "set_edge_last": self.replication_last_set_edge,
                "set_edge_min_dynamic": self._replication_dynamic_min_edge(tte),
                "budget_remaining": self.remaining_budget(),
                "spent_est": self.spent_est,
                "successful_buy_trades": self.successful_buy_trades,
                "session_bought_shares": self.session_bought_shares,
                "max_session_shares": self.max_session_shares,
                "net_imbalance": pos.up.size - pos.down.size,
                "pos_up_size": pos.up.size,
                "pos_dn_size": pos.down.size,
                "up_bid": books.up_bid,
                "up_ask": books.up_ask,
                "up_ask_sz": books.up_ask_sz,
                "dn_bid": books.dn_bid,
                "dn_ask": books.dn_ask,
                "dn_ask_sz": books.dn_ask_sz,
                "skip_top": sorted(self.skip_reasons.items(), key=lambda kv: kv[1], reverse=True)[:8],
                "status_bits": status_bits[:6],
            }
            with pth.open("a", encoding="utf-8") as f:
                f.write(json.dumps(rec, separators=(",", ":"), ensure_ascii=False) + "\n")
        except Exception:
            self.logger.exception("replication_diag_write_failed")

    def try_replication_mode(self, books: TopOfBook, pos: PositionSnapshot):
        if books.up_ask is None or books.dn_ask is None:
            self._record_skip("repl:no_book")
            return
        tte = self.time_to_end_s()
        if tte is None:
            self._record_skip("repl:no_tte")
            return
        if tte <= 0:
            self._record_skip("repl:ended")
            return
        if tte > self.replication_window_s:
            self._record_skip("repl:outside_window")
            return

        now_ts = time.time()
        if now_ts < self.replication_next_trade_ts:
            self._record_skip("repl:cadence_wait")
            return
        self.replication_next_trade_ts = now_ts + self.replication_cadence_s

        ask_sum = books.up_ask + books.dn_ask
        set_edge = 1.0 - self.est_effective_cost(ask_sum)
        self.replication_last_set_edge = set_edge
        dynamic_min_edge = self._replication_dynamic_min_edge(tte)
        if set_edge < dynamic_min_edge:
            self._record_skip("repl:min_edge")
            return

        if not self._can_open_new_buy():
            self._record_skip("buy:max_trades")
            return

        budget = self.remaining_budget()
        if budget <= 0:
            self._record_skip("repl:budget")
            return

        imbalance = pos.up.size - pos.down.size

        # If imbalance exceeds cap, only buy the lighter side to pull inventory back toward neutral.
        if imbalance > self.replication_max_net_imbalance:
            qty = min(
                self.step_shares,
                books.dn_ask_sz or 0.0,
                self.remaining_session_shares(),
                budget / max(1e-9, self.est_effective_cost(books.dn_ask)),
                max(0.0, imbalance - self.replication_max_net_imbalance),
            )
            if qty <= 0 or (not self._meets_min_order(books.dn_ask, qty)):
                self._record_skip("repl:rebalance_down_qty")
                return
            added_paid = self.est_effective_cost(books.dn_ask * qty)
            if self.live and (not self._can_buy_without_breaking_settlement_floor(0.0, qty, added_paid)):
                self._record_skip("repl:rebalance_down_settlement_guard")
                return
            ok, err = self._post_buy(self.meta.token_ids[1], books.dn_ask, qty, "replication rebalance DOWN")
            ts = now_utc().astimezone().strftime("%H:%M:%S")
            action = TradeAction(ts, "BUY", "DOWN", qty, books.dn_ask, self._buy_note("replication rebalance DOWN", books.dn_ask, books.dn_ask), ok, err)
            self.log_action(action)
            if ok:
                self._record_purchase(self.meta.token_ids[1], books.dn_ask, qty)
                self.spent_est += added_paid
            return

        if imbalance < -self.replication_max_net_imbalance:
            qty = min(
                self.step_shares,
                books.up_ask_sz or 0.0,
                self.remaining_session_shares(),
                budget / max(1e-9, self.est_effective_cost(books.up_ask)),
                max(0.0, -imbalance - self.replication_max_net_imbalance),
            )
            if qty <= 0 or (not self._meets_min_order(books.up_ask, qty)):
                self._record_skip("repl:rebalance_up_qty")
                return
            added_paid = self.est_effective_cost(books.up_ask * qty)
            if self.live and (not self._can_buy_without_breaking_settlement_floor(qty, 0.0, added_paid)):
                self._record_skip("repl:rebalance_up_settlement_guard")
                return
            ok, err = self._post_buy(self.meta.token_ids[0], books.up_ask, qty, "replication rebalance UP")
            ts = now_utc().astimezone().strftime("%H:%M:%S")
            action = TradeAction(ts, "BUY", "UP", qty, books.up_ask, self._buy_note("replication rebalance UP", books.up_ask, books.up_ask), ok, err)
            self.log_action(action)
            if ok:
                self._record_purchase(self.meta.token_ids[0], books.up_ask, qty)
                self.spent_est += added_paid
            return

        # Default replication behavior: paired buys (near-complete-set accumulation).
        qty = min(
            self.step_shares,
            books.up_ask_sz or 0.0,
            books.dn_ask_sz or 0.0,
            self.remaining_session_shares(),
            budget / max(1e-9, self.est_effective_cost(ask_sum)),
        )
        if qty <= 0:
            self._record_skip("repl:pair_qty")
            return
        if (not self._meets_min_order(books.up_ask, qty)) or (not self._meets_min_order(books.dn_ask, qty)):
            self._record_skip("repl:pair_min_order")
            return

        added_paid = self.est_effective_cost(books.up_ask * qty) + self.est_effective_cost(books.dn_ask * qty)
        if self.live and (not self._can_buy_without_breaking_settlement_floor(qty, qty, added_paid)):
            self._record_skip("repl:pair_settlement_guard")
            return

        self.opps_met += 1
        ok1, err1 = self._post_buy(self.meta.token_ids[0], books.up_ask, qty, "replication paired buy")
        ok2, err2 = self._post_buy(self.meta.token_ids[1], books.dn_ask, qty, "replication paired buy")
        ts = now_utc().astimezone().strftime("%H:%M:%S")
        self.log_action(TradeAction(ts, "BUY", "UP", qty, books.up_ask, self._buy_note("replication paired buy", books.up_ask, books.up_ask), ok1, err1))
        self.log_action(TradeAction(ts, "BUY", "DOWN", qty, books.dn_ask, self._buy_note("replication paired buy", books.dn_ask, books.dn_ask), ok2, err2))
        if ok1:
            self._record_purchase(self.meta.token_ids[0], books.up_ask, qty)
            self.spent_est += self.est_effective_cost(books.up_ask * qty)
        if ok2:
            self._record_purchase(self.meta.token_ids[1], books.dn_ask, qty)
            self.spent_est += self.est_effective_cost(books.dn_ask * qty)
        if ok1 != ok2:
            self.rebalance_only_mode = True

    def refresh_portfolio_value_api(self, force: bool = False) -> Optional[float]:
        if (not force) and (time.time() - self._portfolio_api_last_ts < self.wallet_refresh_interval_s):
            return self.portfolio_api_value
        self._portfolio_api_last_ts = time.time()
        if (not self.user_addr) or (not self.meta.condition_id):
            return self.portfolio_api_value
        try:
            url = f"{self.data_api_host.rstrip('/')}/positions"
            params = {"user": self.user_addr, "market": self.meta.condition_id, "sizeThreshold": 0}
            r = requests.get(url, params=params, timeout=6)
            r.raise_for_status()
            rows = r.json() or []
            total = 0.0
            have_any = False
            for row in rows:
                v = row.get("currentValue")
                if v is None:
                    v = row.get("curValue", row.get("value"))
                if v is not None:
                    vv = parse_floatish(str(v), 0.0)
                    total += max(0.0, vv)
                    have_any = True
                    continue
                sz = parse_floatish(str(row.get("size", 0.0)), 0.0)
                cp = row.get("curPrice")
                if cp is None:
                    cp = row.get("currentPrice")
                cpv = parse_floatish(str(cp), 0.0)
                total += max(0.0, sz * cpv)
                have_any = True
            if have_any:
                cash = self.wallet_debug.balance if self.wallet_debug.balance is not None else self.max_spend_usd
                self.portfolio_api_value = float(cash) + total
            return self.portfolio_api_value
        except Exception:
            return self.portfolio_api_value

    def _portfolio_balance(self, books: TopOfBook, pos: PositionSnapshot, wallet_debug: WalletDebug) -> float:
        cash = wallet_debug.balance if wallet_debug.balance is not None else self.max_spend_usd
        up_mark = max(0.0, pos.up.size) * max(0.0, (books.up_bid or 0.0))
        dn_mark = max(0.0, pos.down.size) * max(0.0, (books.dn_bid or 0.0))
        return float(cash) + up_mark + dn_mark

    def step(self) -> Tuple[TopOfBook, PositionSnapshot, str, WalletDebug, RuntimeStats, str]:
        self._ensure_runtime_guards()
        self._recheck_pending_fills()
        self.session_bought_shares = self._current_market_session_bought_shares()
        books = self.fetch_books()
        self._last_books = books
        self._fetch_btc_spot(force=self.collect_mode)
        self._sync_market_open_price()
        prev_pos_snapshot = self.last_positions_snapshot
        pos = self.positions()
        if self.live:
            self._reconcile_recent_actions_from_position_delta(prev_pos_snapshot, pos)
        if self.live:
            self._sync_accounting_from_positions(pos)
        else:
            pos = self._paper_position_snapshot()
            self.positions_stale = False
        pos_guard = self._risk_guard_snapshot(pos)
        if self.ml_mode:
            self.spent_est = max(0.0, self.max_spend_usd - self.ml_virtual_cash)
        wallet_debug = self.refresh_wallet_debug()
        portfolio_api = self.refresh_portfolio_value_api(force=False)
        portfolio_balance_now = portfolio_api if portfolio_api is not None else self._portfolio_balance(books, pos, wallet_debug)
        if self.portfolio_start_balance is None:
            self.portfolio_start_balance = portfolio_balance_now
        portfolio_delta_now = portfolio_balance_now - (self.portfolio_start_balance or portfolio_balance_now)
        self.live_locked_pnl_est = pos.hedged * (1.0 - (pos.up.avg_price + pos.down.avg_price))
        runtime_stats = self.compute_runtime_stats(books)
        self._last_runtime_stats = runtime_stats

        # Decision string (for UI)
        decision_lines = []

        ws_state = "n/a"
        if self.price_feed_mode == "ws":
            ws_state = "live" if (self.ws_book and (time.time() - self.ws_last_update_ts) <= 3.0) else f"warming_up/fallback ({self.ws_failure_detail[:80]})"
        skip_summary = ", ".join(f"{k}={v}" for k, v in sorted(self.skip_reasons.items(), key=lambda kv: kv[1], reverse=True)[:6])
        decision_lines.append(
            f"Health: feed={self.price_feed_mode} ({ws_state}) positions_stale={self.positions_stale} pending_fills={len(self.pending_fill_checks)} pending_risk_sells={len(self.pending_risk_sell_checks)} wallet={wallet_debug.status}"
        )
        decision_lines.append(
            "API telemetry: "
            + self._format_api_metric("clob.orderbook")
            + " | "
            + self._format_api_metric("data_api.positions")
        )
        decision_lines.append(f"Skip counters(top): {skip_summary if skip_summary else 'none'}")

        net_imbalance = self._net_imbalance(pos_guard)
        risky_imbalance = self._has_risky_imbalance(pos_guard)
        status_bits: List[str] = []
        hold_risk_sells = (
            self.ml_mode
            or self.replication_mode
            or self.collect_mode
            or bool(self.pending_fill_checks)
            or bool(self.pending_unwind_sell_checks)
            or bool(self.pending_risk_sell_checks)
            or (time.time() < self.pair_fill_grace_until_ts)
        )
        sold_risk = False if hold_risk_sells else self._try_inventory_risk_sell(books, pos_guard)
        if sold_risk:
            status_bits.append("Risk sell executed to reduce one-sided inventory")
        elif hold_risk_sells:
            status_bits.append("Risk sells paused while delayed pair fill/unwind state settles")
        if not risky_imbalance and self.rebalance_only_mode:
            self.rebalance_only_mode = False

        # Always prefer completing existing inventory first, then instant bundle, then build
        if self.book_error:
            decision_lines.append(f"Book fetch error: {self.book_error[:180]}")
            decision_lines.append("No orderbook for this slug/token right now. Pick another active slug.")
            status_bits.append("Market data unavailable; waiting for orderbook")
        elif self.auth_broken and self.live:
            if not self.auth_broken_notice_logged:
                self.auth_broken_notice_logged = True
                self.logger.error("Trading paused for this run because authentication is invalid.")
            decision_lines.append("Trading paused: INVALID_SIGNATURE detected. Restart with SIGNATURE_TYPE=0 for regular wallets.")
            status_bits.append("Paused: auth/signature issue")
        elif self.funds_blocked and self.live:
            if not self.funds_blocked_notice_logged:
                self.funds_blocked_notice_logged = True
                self.logger.error("Trading paused for this run because balance/allowance is insufficient.")
            decision_lines.append("Trading paused: insufficient balance/allowance. See account diagnostics panel.")
            status_bits.append("Paused: insufficient balance/allowance")
        elif self.fee_broken and self.live:
            decision_lines.append("Trading paused: repeated invalid fee-rate errors. Set FEE_RATE_RAW/FEE_RATE_BPS to market fee (e.g., 1000).")
            status_bits.append("Paused: fee config rejected by API")
        elif self.pending_fill_checks:
            self._record_skip("step:pending_fill_hold")
            decision_lines.append("Safety hold: waiting for delayed fill confirmations before placing any new orders.")
            status_bits.append(f"Waiting on {len(self.pending_fill_checks)} delayed fill confirmations")
        elif self.positions_stale and self.live:
            self._record_skip("step:positions_stale")
            decision_lines.append("Safety hold: positions API is stale/unreachable; blocking new BUYs to prevent overexposure.")
            status_bits.append("Positions stale: holding new entries")
            self.try_flip_scalp(books, pos)
        elif self._has_unresolved_exit_risk() and self.live:
            self._record_skip("step:exit_risk_hold")
            decision_lines.append("Safety hold: unresolved SELL failures detected; pausing new BUYs until exits recover.")
            status_bits.append("Exit failures active: no new buys")
            self.try_flip_scalp(books, pos)
        elif sold_risk:
            decision_lines.append("Executed risk-reducing SELL to cut one-sided exposure; deferring new BUYs this cycle.")
        elif self.require_rebuild_after_risk_sell:
            decision_lines.append("Risk-sell reset active: completion buys paused until a new inventory-build buy succeeds.")
            status_bits.append("Reset-after-risk-sell: build inventory first")
        elif self._post_risk_rebalance_cooldown_remaining_s() > 0:
            rem_cd = int(math.ceil(self._post_risk_rebalance_cooldown_remaining_s()))
            decision_lines.append(
                f"Post-risk-sell cooldown active ({rem_cd}s): skipping completion buys to avoid acting on stale inventory snapshots."
            )
            status_bits.append(f"Post-risk-sell completion cooldown {rem_cd}s")
        elif self.scalp_only_mode:
            status_bits.append("Penny scalping mode: watching oscillation pattern for +$0.01 exits")
            self.try_flip_scalp(books, pos)
        elif self.upswing_only_mode:
            status_bits.append("Upswing scalper mode: buying momentum and exiting at TP/SL")
            self.try_upswing_scalp(books, pos)
        elif self.collect_mode:
            status_bits.append("Collect mode: recording market + BTC snapshots (no trading)")
            self._collect_market_sample(books)
        elif self.replication_mode:
            status_bits.append("Replication mode: late-window paired buys with 4s cadence + bounded imbalance")
            self.try_replication_mode(books, pos)
        elif self.ml_mode:
            status_bits.append("ML lab mode: buy-only adaptive paper strategy search")
            self.try_ml_mode(books, pos)
        elif self.hedge_only_mode:
            status_bits.append("Quant hedge mode: protecting draw floor and adding selective upside")
            self._update_flip_history(books)
            self.try_quant_hedge(books, runtime_stats)
        elif self.gpt_mode:
            status_bits.append("GPT mode: blending BTC momentum + orderbook imbalance")
            self._update_flip_history(books)
            self.try_gpt_mode(books, runtime_stats)
        elif self.fortress_mode:
            status_bits.append("Fortress mode: buy-only pair lock with bounded directional tilt")
            self._update_flip_history(books)
            self.try_fortress_mode(books, pos, runtime_stats)
        elif (self.market_open_wait_remaining_s() or 0) > 0:
            remaining_s = self.market_open_wait_remaining_s() or 0
            self._record_skip("step:post_open_wait")
            decision_lines.append(
                f"Post-open hold active: waiting {remaining_s}s before allowing new entries (configured delay={self.market_open_delay_s}s)."
            )
            status_bits.append(f"Post-open wait {remaining_s}s")
        elif risky_imbalance or self.rebalance_only_mode:
            self._record_skip("step:imbalance_hold")
            decision_lines.append(
                f"Safety hold: net imbalance {net_imbalance:.4f} shares exceeds limit {self.max_net_imbalance_shares:.4f}. Rebalance-only mode active."
            )
            status_bits.append(f"Rebalancing exposure (net {net_imbalance:+.2f} shares)")
            self.try_complete_from_inventory(books, pos_guard)
            self.try_flip_scalp(books, pos_guard)
        else:
            status_bits.append("Scanning for instant bundle + completion opportunities")
            self.try_complete_from_inventory(books, pos_guard)
            self.try_instant_bundle(books, pos_guard)
            self.try_build_inventory(books, pos_guard)
            self.try_flip_scalp(books, pos_guard)

        # Build decision text
        if books.up_ask is not None and books.dn_ask is not None:
            ask_sum = books.up_ask + books.dn_ask
            eff_sum = self.est_effective_cost(ask_sum)
            profit = 1.0 - eff_sum
            decision_lines.append(f"Instant bundle check: cost/share={eff_sum:.6f} profit/share={profit:.6f}")
            decision_lines.append(f"Trade triggers when profit >= {self.min_edge:.6f}")
            status_bits.append(f"Bundle edge {profit:.4f} vs trigger {self.min_edge:.4f}")
        else:
            decision_lines.append("Book missing asks on one side.")
            status_bits.append("One side has no ask; cannot bundle yet")

        tte = self.time_to_end_s()
        if tte is not None:
            decision_lines.append(f"Time-to-end computed from slug+interval: {tte}s")
            if tte <= 0:
                decision_lines.append("Market looks ended (negative/zero time-to-end). Use the current slug.")
            elif tte <= 60:
                decision_lines.append("Near expiry: inventory building disabled (<=60s). Hedging still allowed.")

        budget = self.remaining_budget()
        decision_lines.append(f"Remaining budget: {budget:.4f} (spent est: {self.spent_est:.4f})")
        decision_lines.append(f"Held-cost floor applied: up_paid={self.up_paid_total:.4f} down_paid={self.down_paid_total:.4f}")
        decision_lines.append("Max spend source: ml fixed budget" if self.ml_mode else ("Max spend source: wallet live balance" if self.live else "Max spend source: configured paper budget"))
        eff_edge = self.effective_min_edge()
        idle_s = int(max(0.0, time.time() - self.last_success_trade_ts))
        decision_lines.append(f"Fee rate: {self.meta.taker_fee_rate*100:.4f}% (raw {self.fee_rate_raw}, bps-field {self.fee_rate_bps})  tick_size: {self.meta.tick_size:g}")
        decision_lines.append(f"Min order filters: shares>={self.min_order_shares:g} notional>={self.min_order_usd:g}")
        decision_lines.append(f"Session share cap (this market): bought={self.session_bought_shares:.2f} / max={self.max_session_shares:.2f}")
        rem_trades = self.remaining_buy_trades()
        decision_lines.append(
            f"Trade cap: used={self.executed_trade_count} / max={'∞' if rem_trades is None else self.max_trades} (includes buys+sells)"
        )
        decision_lines.append(f"Post-open wait setting: {self.market_open_delay_s}s")
        if not self.disable_flip_scalp or self.scalp_only_mode:
            decision_lines.append(
                f"Flip scalp: enabled={not self.disable_flip_scalp} open_positions={len(self.flip_open)} "
                f"target_move=+{self.flip_target_cents:.3f} stop_loss=-{self.flip_stop_loss_cents:.2f} "
                f"spread_cap<={self.flip_max_spread:.3f} min_edge={self.flip_min_expected_edge:.4f} "
                f"entry_band=[{self.flip_entry_price_min:.2f},{self.flip_entry_price_max:.2f}] max_drift<={self.flip_max_window_drift:.3f} "
                f"pause_s={(max(0.0, self.flip_pause_until_ts - time.time())):.0f} "
                f"hold_hedged_pairs={self.flip_hold_hedged_pairs} hold_edge>={self.flip_hold_min_edge:.3f} reserve_qty={self.flip_hedge_reserve_qty:.2f} "
                f"signal(up/down)={self.flip_signal_debug.get('UP','-')} / {self.flip_signal_debug.get('DOWN','-')}"
            )
        if self.upswing_only_mode:
            decision_lines.append(
                f"Upswing scalp: open_positions={len(self.upswing_open)} tp=+{self.upswing_take_profit_cents:.3f} sl=-{self.upswing_stop_loss_cents:.3f} min_momo={self.upswing_min_momentum_cents:.3f} min_score={self.upswing_min_score:.2f} signal(up/down)={self.upswing_signal_debug.get('UP','-')} / {self.upswing_signal_debug.get('DOWN','-')}"
            )
        if self.ml_mode:
            decision_lines.append(
                f"ML lab (paper buy-only): cash={self.ml_virtual_cash:.4f} equity={self._ml_equity_mark(books):.4f} up={self.ml_up_qty:.4f}@{(self.ml_up_cost/max(1e-9,self.ml_up_qty)) if self.ml_up_qty>0 else 0.0:.4f} down={self.ml_dn_qty:.4f}@{(self.ml_dn_cost/max(1e-9,self.ml_dn_qty)) if self.ml_dn_qty>0 else 0.0:.4f} active={self.ml_active_idx} scores={self.ml_scores} trials={self.ml_trials} signal={self.ml_last_signal}"
            )
        if self.replication_mode:
            decision_lines.append(
                f"Replication: window<={self.replication_window_s:.0f}s cadence={self.replication_cadence_s:.1f}s min_set_edge={self.replication_min_set_edge:.4f} max_net_imbalance={self.replication_max_net_imbalance:.2f} last_set_edge={self.replication_last_set_edge:.4f}"
            )
        pending_pair_count = sum(1 for p in self.pending_pair_unwinds.values() if (not p.get("unwound")) and (not p.get("resolved")))
        decision_lines.append(f"Pair unwind watch (5s one-leg timeout): pending_pairs={pending_pair_count}")
        decision_lines.append(f"Pair unwind sell rechecks: {len(self.pending_unwind_sell_checks)}")
        decision_lines.append(f"Pair fill grace (risk-sell pause): {max(0.0, self.pair_fill_grace_until_ts - time.time()):.1f}s")
        if self.collect_mode:
            decision_lines.append(f"Collect mode: csv={self.collect_data_csv} samples={self.collect_samples_count}")
        if self.replication_mode:
            tte_dbg = self.time_to_end_s()
            dyn_edge_dbg = self._replication_dynamic_min_edge(tte_dbg)
            decision_lines.append(f"Replication dynamic min edge now={dyn_edge_dbg:.4f} (tte={tte_dbg})")
            decision_lines.append(f"Replication diag log: {self.replication_diag_log}")
        if self.flip_open and (not self.disable_flip_scalp or self.scalp_only_mode):
            decision_lines.append(
                f"Flip exit retry: up_fail={self.flip_exit_fail_count.get('UP',0)} down_fail={self.flip_exit_fail_count.get('DOWN',0)}"
            )
        decision_lines.append(f"Strategy mode: {'penny_scalp' if self.scalp_only_mode else ('quant_hedge' if self.hedge_only_mode else ('gpt_mode' if self.gpt_mode else ('fortress' if self.fortress_mode else ('upswing_scalper' if self.upswing_only_mode else ('collect' if self.collect_mode else ('replication' if self.replication_mode else ('ml_lab' if self.ml_mode else 'original_arbitrage')))))))}")
        if not self.ml_mode:
            decision_lines.append(f"Edge target: base={self.min_edge:.6f} effective={eff_edge:.6f} floor={self.min_edge_floor:.6f} idle_since_buy={idle_s}s")
        if (not self.ml_mode) and (not self.collect_mode):
            decision_lines.append(f"Inventory build enabled: {self.allow_inventory_build}")
        decision_lines.append(f"Execution mode: buy_order_type={self.order_type} sell_order_type={self.sell_order_type} require_immediate_fill={self.require_immediate_fill}")
        decision_lines.append(f"Sell price mode: {self.sell_price_mode} undercut={self.sell_undercut_cents:.3f}")
        if not self.ml_mode:
            decision_lines.append(
                f"Risk guard: max_net_imbalance_shares={self.max_net_imbalance_shares:g} net_imbalance_now={net_imbalance:.4f} rebalance_only={self.rebalance_only_mode}"
            )
            decision_lines.append(
                f"Inventory sell guard: max_side={self.max_side_position_shares:.2f} take_profit>={self.inventory_take_profit_cents:.3f} stop_loss<={-self.inventory_stop_loss_cents:.3f}"
            )
        decision_lines.append(f"Settlement guard: floor={self.settle_floor:.4f} up_if_win={runtime_stats.pnl_if_up_wins:.4f} down_if_win={runtime_stats.pnl_if_down_wins:.4f}")
        if self.hedge_only_mode:
            decision_lines.append(
                f"Hedge guard: minor_loss_limit={self.hedge_minor_loss_limit:.4f} upside_alloc={self.hedge_upside_allocation:.2f} max_upside_shares={self.hedge_max_extra_shares:.2f}"
            )
        if self.gpt_mode:
            decision_lines.append(
                f"GPT mode: alloc_frac={self.gpt_alloc_fraction:.2f} min_signal={self.gpt_min_signal:.2f} last={self.gpt_last_signal}"
            )
        if self.fortress_mode:
            decision_lines.append(
                f"Fortress: loss_cap={self.fortress_loss_cap:.3f} lock_edge>={self.fortress_lock_edge:.3f} tilt_budget={self.fortress_tilt_budget:.2f} max_imb={self.fortress_max_imbalance:.2f} max_tilt={self.fortress_max_tilt_shares:.2f}"
            )
        decision_lines.append(f"BTC spot (Binance WS + fast exchange fallback): now={'-' if self._last_btc_price is None else f'{self._last_btc_price:,.2f}'} open={'-' if self.btc_market_open_price is None else f'{self.btc_market_open_price:,.2f}'} source={self.btc_price_source} at={fmt_toronto_hms(self._last_btc_server_ts)} open_source={self.btc_market_open_source} chainlink_stale_after={self.chainlink_stale_after_s:.1f}s low_latency_mode={self.btc_low_latency_mode} ws_pref={self.btc_prefer_ws} btc_ws_age={(-1 if self.btc_ws_last_update_ts<=0 else (time.time()-self.btc_ws_last_update_ts)):.2f}s")
        decision_lines.append(f"Wallet diag: status={wallet_debug.status} usdc={wallet_debug.balance if wallet_debug.balance is not None else '-'} matic={wallet_debug.matic if wallet_debug.matic is not None else '-'} detail={wallet_debug.detail}")
        decision_lines.append(f"Portfolio balance: {portfolio_balance_now:.4f} delta={portfolio_delta_now:+.4f} source={'api' if portfolio_api is not None else 'mark'}")
        status_line = " | ".join(status_bits[:4])
        return books, pos, "\n".join(decision_lines), wallet_debug, runtime_stats, status_line


# ----------------------------
# Rich UI
# ----------------------------

def build_ui(
    meta: MarketMeta,
    books: TopOfBook,
    pos: PositionSnapshot,
    spent: float,
    max_spend: float,
    opps_met: int,
    best_cost: float,
    best_profit: float,
    actions: List[TradeAction],
    decision_text: str,
    wallet_debug: WalletDebug,
    locked_pnl_est: float,
    runtime_stats: RuntimeStats,
    status_bar_text: str,
    poll_interval_s: float,
    price_feed_mode: str,
    ws_last_update_ts: float,
    ws_failure_detail: str,
    btc_spot_price: Optional[float],
    btc_open_price: Optional[float],
    btc_price_source: str,
    btc_last_update_ts: float,
    btc_open_source: str,
    wallet_balance_value: Optional[float],
    portfolio_balance_value: float,
    portfolio_delta_value: float,
    ml_mode: bool,
    ml_up_qty: float,
    ml_dn_qty: float,
    ml_up_avg: float,
    ml_dn_avg: float,
    ml_equity: float,
    html_reports: List[str],
    *,
    live_mode: bool,
    signer_addr: str,
    funder: str,
    signature_type: int,
    user_addr: str,
    log_path: str,
) -> Layout:
    layout = Layout()
    layout.split_column(
        Layout(name="header", size=3),
        Layout(name="body", ratio=1),
        Layout(name="footer", size=2),
    )
    layout["body"].split_row(
        Layout(name="left", ratio=2),
        Layout(name="right", ratio=1),
    )
    layout["left"].split_column(
        Layout(name="market", size=8),
        Layout(name="book", size=7),
        Layout(name="actions", ratio=1),
    )
    layout["right"].split_column(
        Layout(name="account", size=18),
        Layout(name="decision", ratio=1),
    )

    title_base = "ML Learning (buy-only)" if ml_mode else "Polymarket Inventory-Arb (buy-only)"
    title = Text(f"{title_base} [{BOT_VERSION}]", style="bold")
    display_live = live_mode and (not ml_mode)
    status = Text("LIVE" if display_live else "PAPER", style="bold red" if display_live else "bold green")
    header = Table.grid(expand=True)
    header.add_column(justify="left")
    header.add_column(justify="center")
    header.add_column(justify="right")
    header.add_row(title, status, Text("q=quit now, w=quit after current session", style="bold cyan"))
    layout["header"].update(Panel(header, box=box.ROUNDED))

    mkt = Table.grid(padding=(0, 1))
    mkt.add_column(justify="right", style="bold")
    mkt.add_column(justify="left")
    mkt.add_row("Slug", meta.slug)
    mkt.add_row("Question", meta.question)
    mkt.add_row("Outcomes", ", ".join(meta.outcomes))
    mkt.add_row("Interval", f"{meta.interval_s}s")
    mkt.add_row("Signer (EOA from PRIVATE_KEY)", signer_addr)
    mkt.add_row("Signature type", str(signature_type))
    mkt.add_row("Funder", funder)
    mkt.add_row("Wallet used (diag/trading)", user_addr)
    tte = ""
    if meta.end_dt_utc:
        secs = int((meta.end_dt_utc - now_utc()).total_seconds())
        tte = f"{secs}s"
    else:
        tte = "unknown"
    mkt.add_row("Time to end", tte)
    layout["market"].update(Panel(mkt, title="Market", box=box.ROUNDED))

    book = Table(box=box.SIMPLE_HEAVY, expand=True)
    book.add_column("Outcome")
    book.add_column("Bid", justify="right")
    book.add_column("Bid sz", justify="right")
    book.add_column("Ask", justify="right")
    book.add_column("Ask sz", justify="right")

    def row(outcome: str, bid, bid_sz, ask, ask_sz):
        return [
            outcome,
            "-" if bid is None else f"{bid:.4f}",
            "-" if bid_sz is None else f"{bid_sz:.2f}",
            "-" if ask is None else f"{ask:.4f}",
            "-" if ask_sz is None else f"{ask_sz:.2f}",
        ]

    book.add_row(*row("Up", books.up_bid, books.up_bid_sz, books.up_ask, books.up_ask_sz))
    book.add_row(*row("Down", books.dn_bid, books.dn_bid_sz, books.dn_ask, books.dn_ask_sz))
    layout["book"].update(Panel(book, title="Top of Book", box=box.ROUNDED))

    acct = Table.grid(padding=(0, 1))
    acct.add_column(justify="right", style="bold")
    acct.add_column(justify="left")
    acct.add_row("Max spend", fmt_money(max_spend))
    acct.add_row("Wallet balance", "-" if wallet_balance_value is None else fmt_money(wallet_balance_value))
    delta_style = "[green]" if portfolio_delta_value >= 0 else "[red]"
    delta_suffix = "[/green]" if portfolio_delta_value >= 0 else "[/red]"
    acct.add_row("Portfolio balance", f"{fmt_money(portfolio_balance_value)} {delta_style}({portfolio_delta_value:+.4f}){delta_suffix}")
    acct.add_row("Spent (est.)", fmt_money(spent))
    acct.add_row("Remaining budget", fmt_money(max(0.0, max_spend - spent)))
    if ml_mode:
        ml_pnl = ml_equity - max_spend
        ml_pnl_pct = (ml_pnl / max_spend * 100.0) if max_spend > 0 else 0.0
        acct.add_row("ML equity (mark)", fmt_money(ml_equity))
        acct.add_row("ML PnL (mark)", f"{ml_pnl:+.4f} ({ml_pnl_pct:+.2f}%)")
    acct.add_row("Bundles hedged", f"{pos.hedged:.4f}")
    if ml_mode:
        acct.add_row("Held UP shares @ avg", f"{ml_up_qty:.4f} @ {ml_up_avg:.4f}")
        acct.add_row("Held DOWN shares @ avg", f"{ml_dn_qty:.4f} @ {ml_dn_avg:.4f}")
    else:
        acct.add_row("Held UP shares @ avg", f"{pos.up.size:.4f} @ {pos.up.avg_price:.4f}")
        acct.add_row("Held DOWN shares @ avg", f"{pos.down.size:.4f} @ {pos.down.avg_price:.4f}")
    acct.add_row("Unhedged Up", f"{pos.unhedged_up:.4f}")
    acct.add_row("Unhedged Down", f"{pos.unhedged_down:.4f}")
    acct.add_row("Opps met (trades)", str(opps_met))
    acct.add_row("Best eff cost seen", f"{best_cost:.6f}" if best_cost < 1e8 else "-")
    acct.add_row("Best profit/share", f"{best_profit:.6f}" if best_profit > -1e8 else "-")
    acct.add_row("Locked pnl (est)", fmt_money(locked_pnl_est))
    acct.add_row("UP buys / shares", f"{runtime_stats.up_buy_count} / {runtime_stats.up_shares:.4f}")
    acct.add_row("DOWN buys / shares", f"{runtime_stats.down_buy_count} / {runtime_stats.down_shares:.4f}")
    acct.add_row("UP paid / value / PnL", f"{fmt_money(runtime_stats.up_paid)} / {fmt_money(runtime_stats.up_value)} / {fmt_money(runtime_stats.up_pnl)}")
    acct.add_row("DOWN paid / value / PnL", f"{fmt_money(runtime_stats.down_paid)} / {fmt_money(runtime_stats.down_value)} / {fmt_money(runtime_stats.down_pnl)}")
    acct.add_row("Total paid / value / PnL", f"{fmt_money(runtime_stats.total_paid)} / {fmt_money(runtime_stats.total_value)} / {fmt_money(runtime_stats.total_pnl)}")
    acct.add_row("PnL if UP settles @ $1", fmt_money(runtime_stats.pnl_if_up_wins))
    acct.add_row("PnL if DOWN settles @ $1", fmt_money(runtime_stats.pnl_if_down_wins))
    acct.add_row("Wallet diag status", wallet_debug.status)
    acct.add_row("USDC balance", "-" if wallet_debug.balance is None else fmt_money(wallet_debug.balance))
    acct.add_row("MATIC balance", "-" if wallet_debug.matic is None else fmt_money(wallet_debug.matic))
    acct.add_row("Allowance", "-" if wallet_debug.allowance is None else fmt_money(wallet_debug.allowance))
    acct.add_row("Available", "-" if wallet_debug.available is None else fmt_money(wallet_debug.available))
    report_list = "-" if not html_reports else "\n".join([Path(x).name for x in html_reports[-4:]])
    acct.add_row("HTML reports", report_list)
    layout["account"].update(Panel(acct, title="Account", box=box.ROUNDED))

    dec = Panel(Text(decision_text), title="Decision", box=box.ROUNDED)
    layout["decision"].update(dec)

    act_tbl = Table(box=None, expand=True, padding=(0, 0))
    act_tbl.add_column("Time")
    act_tbl.add_column("Action")
    act_tbl.add_column("Side")
    act_tbl.add_column("Shares", justify="right")
    act_tbl.add_column("Unit", justify="right")
    act_tbl.add_column("Note")
    act_tbl.add_column("OK", justify="center")
    for a in actions:
        ok = Text("✔", style="green") if a.ok else Text("✖", style="red")
        note = a.note if a.ok else f"{a.note} | {a.err[:48]}"
        act_tbl.add_row(a.ts, a.action, a.side, f"{a.shares:.2f}", f"{a.unit:.6f}", note, ok)
    layout["actions"].update(Panel(act_tbl, title="Recent Actions", box=box.ROUNDED))

    feed_line = f"Price feed: {price_feed_mode}"
    if price_feed_mode == "ws":
        if ws_last_update_ts > 0:
            ws_age_s = max(0.0, time.time() - ws_last_update_ts)
            ws_state = "LIVE" if ws_age_s <= 3.0 else "STALE->poll fallback"
            feed_line = f"Price feed: ws ({ws_state}, last_update={ws_age_s:.2f}s ago)"
        else:
            detail = ws_failure_detail[:80] if ws_failure_detail else "connecting"
            feed_line = f"Price feed: ws (warming up/fallback: {detail})"

    btc_delta_txt = "n/a"
    if btc_spot_price is not None and btc_open_price is not None and btc_open_price > 0:
        btc_delta_pct = ((btc_spot_price - btc_open_price) / btc_open_price) * 100.0
        btc_delta_txt = f"{btc_delta_pct:+.3f}%"
    footer = Text(
        f"Status: {status_bar_text}\nversion={BOT_VERSION} | {feed_line} | BTC now/open={'-' if btc_spot_price is None else f'{btc_spot_price:,.2f}'}/{'-' if btc_open_price is None else f'{btc_open_price:,.2f}'} ({btc_delta_txt}, src={btc_price_source}, t={fmt_toronto_hms(btc_last_update_ts)}, open_src={btc_open_source}) | poll_interval={poll_interval_s:.2f}s | log={log_path}",
        style="dim",
    )
    layout["footer"].update(Align.left(footer))
    return layout


# ----------------------------
# Keypress handling
# ----------------------------

def pressed_key_action() -> Optional[str]:
    """Return keyboard action: 'quit_now', 'quit_after_session', or None."""
    # Windows
    if os.name == "nt":
        try:
            import msvcrt  # type: ignore
            if msvcrt.kbhit():
                ch = msvcrt.getwch().lower()
                if ch == "q":
                    return "quit_now"
                if ch == "w":
                    return "quit_after_session"
        except Exception:
            return None
        return None

    # Unix fallback: non-blocking stdin
    try:
        import select
        dr, _, _ = select.select([sys.stdin], [], [], 0)
        if dr:
            ch = sys.stdin.read(1).lower()
            if ch == "q":
                return "quit_now"
            if ch == "w":
                return "quit_after_session"
    except Exception:
        pass
    return None


# ----------------------------
# Main
# ----------------------------

def setup_logger(log_path: str) -> logging.Logger:
    logger = logging.getLogger("arb")
    logger.setLevel(logging.DEBUG)

    fmt = logging.Formatter("%(asctime)s %(levelname)s %(message)s")
    fh = RotatingFileHandler(log_path, maxBytes=2_000_000, backupCount=3, encoding="utf-8")
    fh.setLevel(logging.DEBUG)
    fh.setFormatter(fmt)

    sh = logging.StreamHandler(sys.stdout)
    sh.setLevel(logging.ERROR)
    sh.setFormatter(fmt)

    logger.handlers.clear()
    logger.addHandler(fh)
    logger.addHandler(sh)
    return logger

def build_clients(
    host: str,
    chain_id: int,
    private_key: Optional[str],
    signature_type: int,
    funder: Optional[str],
    api_key: Optional[str],
    api_secret: Optional[str],
    api_passphrase: Optional[str],
    logger: logging.Logger,
) -> Tuple[ClobClient, Optional[ClobClient], str]:
    # Public client (read-only)
    public_client = ClobClient(host=host, chain_id=chain_id)

    signer_addr = "unknown"
    if private_key and Account and looks_like_privkey(private_key):
        try:
            signer_addr = Account.from_key(private_key).address
        except Exception:
            signer_addr = "unknown"

    if not private_key:
        logger.warning("No private key found in env; LIVE trading cannot work.")
        return public_client, None, signer_addr

    if not looks_like_privkey(private_key):
        logger.error("Private key format invalid (expected 0x + 64 hex). This will cause INVALID_SIGNATURE. See docs. ")
        return public_client, None, signer_addr

    def _build_api_creds_obj(k: str, s: str, p: str) -> Any:
        """Build ApiCreds across py-clob-client version variants."""
        if ApiCreds is None:
            return {"apiKey": k, "secret": s, "passphrase": p}
        variants = [
            {"apiKey": k, "secret": s, "passphrase": p},
            {"api_key": k, "api_secret": s, "api_passphrase": p},
            {"key": k, "secret": s, "passphrase": p},
        ]
        for kw in variants:
            try:
                return ApiCreds(**kw)
            except TypeError:
                continue
            except Exception:
                continue
        try:
            return ApiCreds(k, s, p)
        except Exception:
            return {"apiKey": k, "secret": s, "passphrase": p}

    # Static CLOB API creds can expire/become invalid and cause 401s.
    # By default, prefer deriving fresh creds from L1 auth each run.
    use_static_creds = parse_boolish(os.getenv("USE_STATIC_CLOB_CREDS"), False)
    creds = None
    if use_static_creds and api_key and api_secret and api_passphrase:
        creds = _build_api_creds_obj(api_key, api_secret, api_passphrase)
    elif api_key and api_secret and api_passphrase:
        logger.info("Ignoring static CLOB creds (USE_STATIC_CLOB_CREDS=false); deriving fresh creds from signer.")

    # Defensive normalization for direct callers.
    if signature_type == 0:
        funder = None

    try:
        authed = ClobClient(
            host=host,
            chain_id=chain_id,
            key=private_key,
            creds=creds,
            signature_type=signature_type,
            funder=funder,
        )
    except Exception:
        logger.exception("Failed to initialize authed client")
        return public_client, None, signer_addr

    # If creds not provided, derive/create them using L1 (docs) :contentReference[oaicite:9]{index=9}
    if creds is None:
        try:
            logger.info("Deriving/creating API creds via L1… signature_type=%s funder=%s signer=%s", signature_type, funder, signer_addr)
            api_creds = authed.create_or_derive_api_key()  # some versions name this create_or_derive_api_key
            # Some versions use create_or_derive_api_creds / create_or_derive_api_key; try both
        except AttributeError:
            try:
                api_creds = authed.create_or_derive_api_creds()
            except Exception:
                logger.exception("Failed to derive/create API creds")
                return public_client, authed, signer_addr
        except Exception:
            logger.exception("Failed to derive/create API creds")
            return public_client, authed, signer_addr

        try:
            # Re-init with explicit creds for clarity
            authed = ClobClient(
                host=host,
                chain_id=chain_id,
                key=private_key,
                creds=api_creds,
                signature_type=signature_type,
                funder=funder,
            )
        except Exception:
            logger.exception("Failed to re-init authed client with derived creds")
            # Keep previous authed client anyway
    return public_client, authed, signer_addr

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slug", help="Polymarket market slug or full event URL")
    ap.add_argument("--poll", type=float, default=0.5, help="Polling interval seconds")
    ap.add_argument("--market-universe", choices=["btc", "crypto5m"], default="crypto5m", help="Market scope: BTC-only or all current 5m crypto up/down markets")
    ap.add_argument("--market-selection", choices=["individual", "all"], default="individual", help="Choose a single market to trade or scan all markets")
    ap.add_argument("--paper", action="store_true", help="Run in simulation mode (paper trading)")
    ap.add_argument("--max-spend", type=float, default=50.0, help="Max USD to spend per run")
    ap.add_argument("--min-edge", type=float, default=0.005, help="Min locked profit per share to trade")
    ap.add_argument("--build-max", type=float, default=0.49, help="Only build inventory when ask <= this")
    ap.add_argument("--step", type=float, default=5.0, help="Max shares per action")
    ap.add_argument("--unhedged-usd-max", type=float, default=10.0, help="Max unhedged USD exposure before stopping inventory builds")
    ap.add_argument("--signature-type", type=int, default=None, help="Override signature type (0 EOA, 1 proxy, 2 gnosis safe)")
    ap.add_argument("--env", default=".env", help="Path to .env")
    ap.add_argument("--log", default="arb_debug.log", help="Log file path")
    ap.add_argument("--trade-csv-dir", default="trade_csv", help="Directory for per-market trade CSV exports (Toronto timezone)")
    ap.add_argument("--trade-html-dir", default="trade_html", help="Directory for per-market trade HTML exports")
    ap.add_argument("--alt-screen", action="store_true", help="Use terminal alternate screen mode for Rich UI")
    ap.add_argument("--ui-update-interval", type=float, default=parse_floatish(os.getenv("UI_UPDATE_INTERVAL_S"), 0.75), help="Seconds between terminal UI redraws (higher = less flicker over SSH)")
    ap.add_argument("--market-url", help="Polymarket event URL (alternative to --slug)")
    ap.add_argument("--no-menu", action="store_true", help="Disable startup slug selection menu")
    ap.add_argument("--min-order-shares", type=float, default=5.0, help="Skip orders below this share size")
    ap.add_argument("--min-order-usd", type=float, default=1.0, help="Skip orders below this notional in USD")
    ap.add_argument("--max-session-shares", type=float, default=15.0, help="Maximum total BUY shares per market session")
    ap.add_argument("--max-trades", type=int, default=0, help="Maximum total executed trades this run (buy+sell, 0 = unlimited). Exit sells are always allowed.")
    ap.add_argument("--market-open-delay-s", type=int, choices=[5, 10, 15, 30], default=5, help="Seconds to wait after market open before allowing entries")
    ap.add_argument("--hedge-minor-loss-limit", type=float, default=1.0, help="Hedge mode: keep worst-case settlement PnL above -this USD when possible")
    ap.add_argument("--hedge-upside-allocation", type=float, default=0.35, help="Hedge mode: fraction of safety buffer usable for directional upside adds")
    ap.add_argument("--hedge-max-extra-shares", type=float, default=2.0, help="Hedge mode: max shares per directional upside add")
    ap.add_argument("--gpt-alloc-fraction", type=float, default=0.35, help="GPT mode: fraction of remaining budget allocated per qualified signal")
    ap.add_argument("--gpt-min-signal", type=float, default=0.55, help="GPT mode: minimum model signal strength (0-1) before entering")
    ap.add_argument("--fortress-loss-cap", type=float, default=1.0, help="Fortress mode: max tolerated worst-case settlement loss in USD")
    ap.add_argument("--fortress-lock-edge", type=float, default=0.006, help="Fortress mode: minimum positive lock edge to buy both sides")
    ap.add_argument("--fortress-tilt-budget", type=float, default=0.25, help="Fortress mode: fraction of cushion used for directional tilt")
    ap.add_argument("--fortress-max-imbalance", type=float, default=1.0, help="Fortress mode: max allowed net directional imbalance in shares")
    ap.add_argument("--fortress-max-tilt-shares", type=float, default=2.0, help="Fortress mode: max shares per directional tilt action")
    ap.add_argument("--disable-flip-scalp", action="store_true", help="Disable fluctuation scalp mode (buy then sell +$0.01)")
    ap.add_argument("--strategy-mode", choices=["auto", "scalp", "upswing", "ml", "replicate", "collect", "arb", "hedge", "gpt", "fortress"], default="auto", help="Startup strategy selector: auto popup, scalp, upswing, ml, replicate, collect, hedge, gpt, fortress, or original arbitrage")
    ap.add_argument("--aggressive-edge-relax", action="store_true", help="Aggressively relax min-edge when no fills occur (sets EDGE_RELAX_AFTER_S=45 and MIN_EDGE_FLOOR=0.0005 unless already set)")
    ap.add_argument("--allow-inventory-build", action=argparse.BooleanOptionalAction, default=True, help="Allow one-sided inventory building (on by default; use --no-allow-inventory-build to disable)")
    ap.add_argument("--settle-floor", type=float, default=0.0, help="Minimum required PnL for BOTH settlement outcomes after each buy")
    ap.add_argument("--max-net-imbalance-shares", type=float, default=parse_floatish(os.getenv("MAX_NET_IMBALANCE_SHARES"), 1.0), help="Pause new directional buys when |UP-DOWN| exceeds this")
    ap.add_argument("--max-side-position-shares", type=float, default=10.0, help="Force inventory-reducing sells when either side exceeds this share count")
    ap.add_argument("--inventory-take-profit-cents", type=float, default=0.02, help="For risk-rebalance sells, treat >= this per-share gain as favorable")
    ap.add_argument("--inventory-stop-loss-cents", type=float, default=0.03, help="For risk-rebalance sells, treat <= this per-share loss as urgent")
    ap.add_argument("--upswing-take-profit-cents", type=float, default=0.02, help="Upswing scalper: limit-sell target above entry")
    ap.add_argument("--upswing-stop-loss-cents", type=float, default=0.02, help="Upswing scalper: protective stop below entry")
    ap.add_argument("--upswing-min-momentum-cents", type=float, default=0.012, help="Upswing scalper: minimum short-window momentum needed")
    ap.add_argument("--upswing-min-score", type=float, default=3.2, help="Upswing scalper: minimum signal score to enter")
    ap.add_argument("--price-feed", choices=["poll", "ws"], default=os.getenv("PRICE_FEED", "poll"), help="Price feed mode: polling or websocket")
    ap.add_argument("--ws-url", default=os.getenv("WS_URL", "wss://ws-subscriptions-clob.polymarket.com/ws/market"), help="Websocket URL for market feed")
    ap.add_argument("--sell-order-type", choices=["FAK", "IOC", "FOK", "GTC"], default="FAK", help="Order type for SELL exits; FAK maps to IOC")
    ap.add_argument("--sell-price-mode", choices=["bid", "ask", "ask_minus", "bid_minus"], default="bid", help="How sell limit price is chosen")
    ap.add_argument("--sell-undercut-cents", type=float, default=0.03, help="Price undercut used by ask_minus/bid_minus sell modes")
    ap.add_argument("--ml-start-cash", type=float, default=100.0, help="ML lab mode virtual starting cash (paper only)")
    ap.add_argument("--repl-window-s", type=float, default=parse_floatish(os.getenv("REPL_WINDOW_S"), 240.0), help="Replication mode: only trade in final N seconds before market end")
    ap.add_argument("--repl-cadence-s", type=float, default=parse_floatish(os.getenv("REPL_CADENCE_S"), 4.0), help="Replication mode: minimum seconds between trade attempts")
    ap.add_argument("--repl-min-set-edge", type=float, default=parse_floatish(os.getenv("REPL_MIN_SET_EDGE"), 0.002), help="Replication mode: minimum complete-set edge after fee")
    ap.add_argument("--repl-max-net-imbalance", type=float, default=parse_floatish(os.getenv("REPL_MAX_NET_IMBALANCE"), 150.0), help="Replication mode: max |UP-DOWN| shares before rebalance-only buys")
    ap.add_argument("--repl-diag-log", default=os.getenv("REPL_DIAG_LOG", "replication_diag.jsonl"), help="Replication mode diagnostics JSONL output path")
    ap.add_argument("--collect-data-csv", default=os.getenv("COLLECT_DATA_CSV", "market_collect.csv"), help="Collect mode output CSV path")
    args = ap.parse_args()
    live_mode = not args.paper

    os.environ["MAX_NET_IMBALANCE_SHARES"] = str(args.max_net_imbalance_shares)
    os.environ["REPL_WINDOW_S"] = str(args.repl_window_s)
    os.environ["REPL_CADENCE_S"] = str(args.repl_cadence_s)
    os.environ["REPL_MIN_SET_EDGE"] = str(args.repl_min_set_edge)
    os.environ["REPL_MAX_NET_IMBALANCE"] = str(args.repl_max_net_imbalance)
    if args.aggressive_edge_relax:
        os.environ.setdefault("EDGE_RELAX_AFTER_S", "45")
        os.environ.setdefault("MIN_EDGE_FLOOR", "0.0005")

    load_dotenv(args.env)

    logger = setup_logger(args.log)
    console = Console()

    strategy_mode = args.strategy_mode
    if strategy_mode == "auto":
        if sys.stdin.isatty():
            picked = select_strategy_mode_interactive(console)
            strategy_mode = picked or "arb"
        else:
            strategy_mode = "arb"
    scalp_only_mode = strategy_mode == "scalp"
    hedge_only_mode = strategy_mode == "hedge"
    gpt_mode = strategy_mode == "gpt"
    fortress_mode = strategy_mode == "fortress"
    upswing_only_mode = strategy_mode == "upswing"
    replication_mode = strategy_mode == "replicate"
    collect_mode = strategy_mode == "collect"
    ml_mode = strategy_mode == "ml"
    if ml_mode:
        args.max_spend = 200.0
    if collect_mode and args.price_feed != "ws":
        args.price_feed = "ws"
    disable_flip_scalp = args.disable_flip_scalp or (strategy_mode in {"arb", "hedge", "gpt", "fortress", "upswing", "ml", "replicate", "collect"})
    if scalp_only_mode and sys.stdin.isatty():
        select_scalp_settings_interactive(console, args)
    selected_market_symbol: Optional[str] = None
    if strategy_mode == "arb" and sys.stdin.isatty():
        select_arb_settings_interactive(console, args)
        selected_market_symbol = select_market_symbol_interactive(console)
        os.environ["MAX_NET_IMBALANCE_SHARES"] = str(args.max_net_imbalance_shares)
        if args.aggressive_edge_relax:
            os.environ["EDGE_RELAX_AFTER_S"] = "45"
            os.environ["MIN_EDGE_FLOOR"] = "0.0005"
    if upswing_only_mode and sys.stdin.isatty():
        select_upswing_settings_interactive(console, args)
    if hedge_only_mode and sys.stdin.isatty():
        select_hedge_settings_interactive(console, args)
    if gpt_mode and sys.stdin.isatty():
        select_gpt_settings_interactive(console, args)
    if fortress_mode and sys.stdin.isatty():
        select_fortress_settings_interactive(console, args)

    # Hosts
    clob_host = os.getenv("CLOB_HOST") or os.getenv("CLOB_API_URL") or "https://clob.polymarket.com"
    gamma_host = os.getenv("GAMMA_HOST") or "https://gamma-api.polymarket.com"
    data_api_host = os.getenv("DATA_API_HOST") or "https://data-api.polymarket.com"
    rpc_from_env = parse_csv_urls(os.getenv("POLYGON_RPC_URLS"))
    single_rpc = os.getenv("POLYGON_RPC_URL")
    if single_rpc:
        rpc_from_env = [single_rpc] + [u for u in rpc_from_env if u != single_rpc]
    polygon_rpc_urls = rpc_from_env or [
        "https://polygon-rpc.com",
        "https://polygon-bor-rpc.publicnode.com",
        "https://rpc.ankr.com/polygon",
    ]

    # Keys/params
    private_key = os.getenv("POLYMARKET_PRIVATE_KEY") or os.getenv("PRIVATE_KEY") or os.getenv("PK")
    chain_id = parse_intish(os.getenv("CHAIN_ID"), 137)

    signature_type_env_raw = os.getenv("POLYMARKET_SIGNATURE_TYPE") or os.getenv("SIGNATURE_TYPE")
    signature_type_env = parse_intish(signature_type_env_raw, 1)

    funder = os.getenv("POLYMARKET_FUNDER") or os.getenv("FUNDER_ADDRESS") or os.getenv("FUNDER")

    if args.signature_type is not None:
        signature_type = args.signature_type
    elif signature_type_env_raw:
        signature_type = signature_type_env
    else:
        # If a funder is set, default to proxy auth (email/magic wallet flows).
        signature_type = 1 if funder else 0

    signature_type, funder, auth_mode = resolve_auth_params(signature_type, funder, logger)

    # Optional L2 creds
    api_key = os.getenv("CLOB_API_KEY")
    api_secret = os.getenv("CLOB_SECRET")
    api_passphrase = os.getenv("CLOB_PASS_PHRASE")

    if selected_market_symbol:
        selected_slug = choose_symbol_slug(gamma_host, logger, selected_market_symbol)
    elif args.market_universe == "crypto5m":
        universe = fetch_current_crypto_5m_slugs(gamma_host, logger)
        if args.market_selection == "individual":
            candidates = [(slug, datetime.fromtimestamp(infer_start_ts_from_slug(slug), tz=timezone.utc) if infer_start_ts_from_slug(slug) else None) for slug in universe]
            if sys.stdin.isatty() and candidates:
                picked = select_slug_interactive(console, candidates)
                selected_slug = picked or (universe[0] if universe else current_btc_5m_slug())
            else:
                selected_slug = universe[0] if universe else current_btc_5m_slug()
        else:
            selected_slug = universe[0] if universe else current_btc_5m_slug()
    else:
        selected_slug = current_btc_5m_slug()

    logger.info("START slug=%s live=%s max_spend=%.4f poll=%.2f chain_id=%s signature_type=%s auth_mode=%s funder=%s market_universe=%s market_selection=%s",
                selected_slug, live_mode, args.max_spend, args.poll, chain_id, signature_type, auth_mode, funder, args.market_universe, args.market_selection)
    logger.info("STRATEGY mode=%s scalp_only=%s upswing_only=%s replication_mode=%s collect_mode=%s ml_mode=%s hedge_only=%s gpt_mode=%s fortress_mode=%s flip_scalp_enabled=%s", strategy_mode, scalp_only_mode, upswing_only_mode, replication_mode, collect_mode, ml_mode, hedge_only_mode, gpt_mode, fortress_mode, not disable_flip_scalp)

    # Market meta
    try:
        meta = fetch_market_meta(gamma_host, selected_slug, logger)
    except Exception:
        logger.exception("Failed to fetch market meta from Gamma")
        print("Failed to fetch market meta from Gamma. Check slug.")
        sys.exit(1)

    if len(meta.token_ids) < 2:
        print("Could not discover 2 token IDs for this market. Gamma response likely missing clobTokenIds.")
        print("Check Gamma Get market by slug docs and verify slug.")  # :contentReference[oaicite:10]{index=10}
        sys.exit(1)

    # Clients
    public_client, authed_client, signer_addr = build_clients(
        host=clob_host,
        chain_id=chain_id,
        private_key=private_key,
        signature_type=signature_type,
        funder=funder,
        api_key=api_key,
        api_secret=api_secret,
        api_passphrase=api_passphrase,
        logger=logger,
    )

    if live_mode and authed_client is None:
        print("LIVE mode requested but authenticated client could not be created. Check .env.")
        sys.exit(1)

    if args.market_universe == "crypto5m" and args.market_selection == "all":
        best_slug = choose_best_slug_by_ask_sum(gamma_host, public_client, logger)
        if best_slug and best_slug != meta.slug:
            try:
                meta = fetch_market_meta(gamma_host, best_slug, logger)
                logger.info("Initial all-market selection picked slug=%s", best_slug)
            except Exception:
                logger.exception("initial_all_market_pick_failed")

    # In Polymarket docs: signature type values 0/1/2 and funder rules :contentReference[oaicite:11]{index=11}
    # For positions, use funder for proxy/safe wallets; for EOA use signer address.
    user_addr = funder if signature_type in (1, 2) else signer_addr
    if not user_addr or not user_addr.startswith("0x"):
        user_addr = signer_addr

    trader = Trader(
        public_client=public_client,
        authed_client=authed_client,
        meta=meta,
        poll_s=args.poll,
        live=live_mode,
        max_spend_usd=args.max_spend,
        min_edge=args.min_edge,
        build_max=args.build_max,
        step_shares=args.step,
        unhedged_usd_max=args.unhedged_usd_max,
        data_api_host=data_api_host,
        user_addr=user_addr,
        logger=logger,
        signature_type=signature_type,
        funder=funder,
        polygon_rpc_urls=polygon_rpc_urls,
        min_order_shares=args.min_order_shares,
        min_order_usd=args.min_order_usd,
        max_session_shares=args.max_session_shares,
        max_trades=args.max_trades,
        market_open_delay_s=args.market_open_delay_s,
        disable_flip_scalp=disable_flip_scalp,
        scalp_only_mode=scalp_only_mode,
        upswing_only_mode=upswing_only_mode,
        ml_mode=ml_mode,
        replication_mode=replication_mode,
        collect_mode=collect_mode,
        hedge_only_mode=hedge_only_mode,
        gpt_mode=gpt_mode,
        fortress_mode=fortress_mode,
        gpt_alloc_fraction=args.gpt_alloc_fraction,
        gpt_min_signal=args.gpt_min_signal,
        fortress_loss_cap=args.fortress_loss_cap,
        fortress_lock_edge=args.fortress_lock_edge,
        fortress_tilt_budget=args.fortress_tilt_budget,
        fortress_max_imbalance=args.fortress_max_imbalance,
        fortress_max_tilt_shares=args.fortress_max_tilt_shares,
        hedge_minor_loss_limit=args.hedge_minor_loss_limit,
        hedge_upside_allocation=args.hedge_upside_allocation,
        hedge_max_extra_shares=args.hedge_max_extra_shares,
        max_side_position_shares=args.max_side_position_shares,
        inventory_take_profit_cents=args.inventory_take_profit_cents,
        inventory_stop_loss_cents=args.inventory_stop_loss_cents,
        sell_order_type=args.sell_order_type,
        sell_price_mode=args.sell_price_mode,
        sell_undercut_cents=args.sell_undercut_cents,
        upswing_take_profit_cents=args.upswing_take_profit_cents,
        upswing_stop_loss_cents=args.upswing_stop_loss_cents,
        upswing_min_momentum_cents=args.upswing_min_momentum_cents,
        upswing_min_score=args.upswing_min_score,
        ml_start_cash=args.ml_start_cash,
        replication_diag_log=args.repl_diag_log,
        collect_data_csv=args.collect_data_csv,
        allow_inventory_build=args.allow_inventory_build,
        settle_floor=args.settle_floor,
        price_feed_mode=args.price_feed,
        ws_url=args.ws_url,
    )
    logger.info("")
    logger.info("================ MARKET START ================")
    logger.info("market_slug=%s question=%s start_utc=%s end_utc=%s", meta.slug, meta.question, meta.start_dt_utc, meta.end_dt_utc)
    logger.info("==============================================")
    logger.info("")

    initial_wallet_diag = trader.refresh_wallet_debug(force=True)
    logger.info(
        "WALLET_DIAG status=%s usdc=%s matic=%s allowance=%s available=%s detail=%s",
        initial_wallet_diag.status,
        initial_wallet_diag.balance,
        initial_wallet_diag.matic,
        initial_wallet_diag.allowance,
        initial_wallet_diag.available,
        initial_wallet_diag.detail,
    )

    # Max spend follows wallet balance when available.
    if live_mode and (not ml_mode) and initial_wallet_diag.balance is not None and initial_wallet_diag.balance > 0:
        trader.max_spend_usd = float(initial_wallet_diag.balance)
        logger.info("Max spend set from wallet USDC balance: %.4f", trader.max_spend_usd)

    # Main loop
    best_cost = 1e9
    best_profit = -1e9
    generated_html_reports: List[str] = []
    auto_switched_from_slug: Optional[str] = None
    next_auto_switch_allowed_ts = 0.0
    quit_after_session = False

    ui_update_interval_s = max(0.05, float(args.ui_update_interval))
    if os.getenv("SSH_CONNECTION") or os.getenv("SSH_TTY"):
        ui_update_interval_s = max(ui_update_interval_s, 1.0)

    last_ui_update_ts = 0.0

    with Live(console=console, refresh_per_second=4, screen=args.alt_screen) as live:
        while True:
            key_action = pressed_key_action()
            if key_action == "quit_now":
                break
            if key_action == "quit_after_session":
                quit_after_session = True
                logger.info("Deferred quit armed: will exit when current market session rolls over.")

            try:
                books, pos, decision, wallet_debug, runtime_stats, status_bar_text = trader.step()
                if quit_after_session:
                    status_bar_text = f"Deferred quit armed; exiting at next market rollover | {status_bar_text}"

                tte = trader.time_to_end_s()
                if (
                    tte is not None
                    and tte <= 5
                    and auto_switched_from_slug != meta.slug
                    and time.time() >= next_auto_switch_allowed_ts
                ):
                    prev_slug = meta.slug
                    if args.market_universe == "crypto5m" and args.market_selection == "all":
                        next_slug = choose_best_slug_by_ask_sum(gamma_host, public_client, logger)
                        if not next_slug:
                            next_slug = shift_slug_by_intervals(prev_slug, 1)
                    else:
                        next_slug = shift_slug_by_intervals(prev_slug, 1)
                    if quit_after_session:
                        trader.export_trade_csv(args.trade_csv_dir, tz_name="America/Toronto")
                        html_path = trader.export_trade_html(args.trade_html_dir, tz_name="America/Toronto")
                        if html_path:
                            generated_html_reports = (generated_html_reports + [html_path])[-8:]
                        logger.info("Deferred quit triggered at market rollover. from_slug=%s next_slug=%s", prev_slug, next_slug)
                        break
                    trader.export_trade_csv(args.trade_csv_dir, tz_name="America/Toronto")
                    html_path = trader.export_trade_html(args.trade_html_dir, tz_name="America/Toronto")
                    if html_path:
                        generated_html_reports = (generated_html_reports + [html_path])[-8:]
                    logger.info("Auto-switching to next market because %ss left. from_slug=%s next_slug=%s", tte, prev_slug, next_slug)
                    try:
                        meta = fetch_market_meta(gamma_host, next_slug, logger)
                        logger.info("")
                        logger.info("================ MARKET SWITCH ===============")
                        logger.info("from_slug=%s to_slug=%s question=%s start_utc=%s end_utc=%s", prev_slug, meta.slug, meta.question, meta.start_dt_utc, meta.end_dt_utc)
                        logger.info("==============================================")
                        logger.info("")
                        trader = Trader(
                            public_client=public_client,
                            authed_client=authed_client,
                            meta=meta,
                            poll_s=args.poll,
                            live=live_mode,
                            max_spend_usd=trader.max_spend_usd,
                            min_edge=args.min_edge,
                            build_max=args.build_max,
                            step_shares=args.step,
                            unhedged_usd_max=args.unhedged_usd_max,
                            data_api_host=data_api_host,
                            user_addr=user_addr,
                            logger=logger,
                            signature_type=signature_type,
                            funder=funder,
                            polygon_rpc_urls=polygon_rpc_urls,
                            min_order_shares=args.min_order_shares,
                            min_order_usd=args.min_order_usd,
                            max_session_shares=args.max_session_shares,
                            max_trades=args.max_trades,
                            market_open_delay_s=args.market_open_delay_s,
                            disable_flip_scalp=disable_flip_scalp,
                            scalp_only_mode=scalp_only_mode,
                            upswing_only_mode=upswing_only_mode,
                            ml_mode=ml_mode,
                            replication_mode=replication_mode,
                            collect_mode=collect_mode,
                            hedge_only_mode=hedge_only_mode,
                            gpt_mode=gpt_mode,
                            fortress_mode=fortress_mode,
                            gpt_alloc_fraction=args.gpt_alloc_fraction,
                            gpt_min_signal=args.gpt_min_signal,
                            fortress_loss_cap=args.fortress_loss_cap,
                            fortress_lock_edge=args.fortress_lock_edge,
                            fortress_tilt_budget=args.fortress_tilt_budget,
                            fortress_max_imbalance=args.fortress_max_imbalance,
                            fortress_max_tilt_shares=args.fortress_max_tilt_shares,
                            hedge_minor_loss_limit=args.hedge_minor_loss_limit,
                            hedge_upside_allocation=args.hedge_upside_allocation,
                            hedge_max_extra_shares=args.hedge_max_extra_shares,
                            max_side_position_shares=args.max_side_position_shares,
                            inventory_take_profit_cents=args.inventory_take_profit_cents,
                            inventory_stop_loss_cents=args.inventory_stop_loss_cents,
                            sell_order_type=args.sell_order_type,
                            sell_price_mode=args.sell_price_mode,
                            sell_undercut_cents=args.sell_undercut_cents,
                            upswing_take_profit_cents=args.upswing_take_profit_cents,
                            upswing_stop_loss_cents=args.upswing_stop_loss_cents,
                            upswing_min_momentum_cents=args.upswing_min_momentum_cents,
                            upswing_min_score=args.upswing_min_score,
                            ml_start_cash=args.ml_start_cash,
                            replication_diag_log=args.repl_diag_log,
                            collect_data_csv=args.collect_data_csv,
                            allow_inventory_build=args.allow_inventory_build,
                            settle_floor=args.settle_floor,
                            price_feed_mode=args.price_feed,
                            ws_url=args.ws_url,
                        )
                        wallet_after_switch = trader.refresh_wallet_debug(force=True)
                        if live_mode and (not ml_mode) and wallet_after_switch.balance is not None and wallet_after_switch.balance > 0:
                            trader.max_spend_usd = float(wallet_after_switch.balance)
                            logger.info("Max spend reset from wallet after market switch: %.4f", trader.max_spend_usd)
                        trader.generated_html_reports = generated_html_reports[:]
                        books, pos, decision, wallet_debug, runtime_stats, status_bar_text = trader.step()
                        best_cost = 1e9
                        best_profit = -1e9
                        auto_switched_from_slug = prev_slug
                        next_auto_switch_allowed_ts = time.time() + 15.0
                    except Exception:
                        logger.exception("auto_market_switch_failed")
                        next_auto_switch_allowed_ts = time.time() + 5.0

                best_cost = min(best_cost, trader.best_cost_seen)
                best_profit = max(best_profit, trader.best_profit_per_bundle)

                ui = build_ui(
                    meta=meta,
                    books=books,
                    pos=pos,
                    spent=trader.spent_est,
                    max_spend=trader.max_spend_usd,
                    opps_met=trader.opps_met,
                    best_cost=best_cost,
                    best_profit=best_profit,
                    actions=trader.actions,
                    decision_text=decision,
                    wallet_debug=wallet_debug,
                    locked_pnl_est=(trader.live_locked_pnl_est if live_mode else trader.paper_locked_pnl),
                    runtime_stats=runtime_stats,
                    status_bar_text=status_bar_text,
                    poll_interval_s=args.poll,
                    price_feed_mode=trader.price_feed_mode,
                    ws_last_update_ts=trader.ws_last_update_ts,
                    ws_failure_detail=trader.ws_failure_detail,
                    btc_spot_price=trader._last_btc_price,
                    btc_open_price=trader.btc_market_open_price,
                    btc_price_source=trader.btc_price_source,
                    btc_last_update_ts=trader._last_btc_server_ts,
                    btc_open_source=trader.btc_market_open_source,
                    wallet_balance_value=wallet_debug.balance,
                    portfolio_balance_value=((trader.portfolio_api_value if trader.portfolio_api_value is not None else trader._portfolio_balance(books, pos, wallet_debug))),
                    portfolio_delta_value=(((trader.portfolio_api_value if trader.portfolio_api_value is not None else trader._portfolio_balance(books, pos, wallet_debug)) - (trader.portfolio_start_balance or (trader.portfolio_api_value if trader.portfolio_api_value is not None else trader._portfolio_balance(books, pos, wallet_debug))))),
                    ml_mode=ml_mode,
                    ml_up_qty=trader.ml_up_qty,
                    ml_dn_qty=trader.ml_dn_qty,
                    ml_up_avg=(trader.ml_up_cost / max(1e-9, trader.ml_up_qty) if trader.ml_up_qty > 0 else 0.0),
                    ml_dn_avg=(trader.ml_dn_cost / max(1e-9, trader.ml_dn_qty) if trader.ml_dn_qty > 0 else 0.0),
                    ml_equity=trader._ml_equity_mark(books),
                    html_reports=(generated_html_reports if generated_html_reports else trader.generated_html_reports),
                    live_mode=live_mode,
                    signer_addr=signer_addr,
                    funder=safe_addr(funder),
                    signature_type=signature_type,
                    user_addr=user_addr,
                    log_path=args.log,
                )
                now_ui_ts = time.time()
                if (now_ui_ts - last_ui_update_ts) >= ui_update_interval_s:
                    live.update(ui)
                    last_ui_update_ts = now_ui_ts
            except Exception as e:
                logger.exception("loop_error")
                live.update(Panel(Text(f"Loop error: {e}\nSee log: {args.log}"), title="Runtime Error", box=box.ROUNDED))
                # Keep UI alive even on intermittent failures

            time.sleep(max(0.05, args.poll))

    trader.export_trade_csv(args.trade_csv_dir, tz_name="America/Toronto")
    html_path = trader.export_trade_html(args.trade_html_dir, tz_name="America/Toronto")
    if html_path:
        generated_html_reports = (generated_html_reports + [html_path])[-8:]
    print(f"Exited. Log written to: {args.log}")

if __name__ == "__main__":
    # Needed because we used timedelta in fetch_market_meta
    from datetime import timedelta
    main()
