#!/usr/bin/env python3
"""크롬하츠(chromehearts.com) 전용 쪽감시자: 신상품 등록, 재입고/판매 시작,
개별 상품 구매 가능(Add to Bag) 전환을 Discord로 알림.

- catalog      : 카테고리 목록 페이지(예: /scents, /socks)를 감시. 신규 상품, 품절→구매가능
                 재입고, (옵션) 구매가능→품절 변경을 상품코드(PID) 기준으로 추적.
- availability : 개별 상품 상세 페이지의 Add to Bag / Sold Out / Coming Soon 상태 감시.
- 상세 자동 추적: 발견한 상품의 공개 Product-Variation 응답으로 색상/사이즈별 상태 확인.
                 주문 수량 제한을 재고량으로 사용하지 않으며 기본 수량 표시는 '미공개'.
- 카테고리 탐색: 다단계 링크, robots.txt, sitemap/index와 중간 분류 페이지를 확인.
                  후보/출처/제외/실패/범위 제한은 state의 discovery_audit에 기록.
- 알림 큐      : state 파일에 미전송 이벤트를 저장하고 전송 성공한 이벤트만 제거.
- items/region : 범용 모드(선택자 기반)로 그대로 유지.

로그인 쿠키를 요청하거나 외부 서버에 인증정보를 보내지 않습니다. 403/429/캡차는
우회하지 않고 대기합니다. 기본값은 첫 실행 알림 없음입니다.
"""
from __future__ import annotations

import argparse
from collections import deque
from contextlib import ExitStack
from contextvars import ContextVar
import copy
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
import gzip
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import unicodedata
from urllib.parse import urljoin, urlsplit, urlunsplit, parse_qsl, urlencode, unquote
import xml.etree.ElementTree as ET
from zoneinfo import ZoneInfo

from bs4 import BeautifulSoup
import requests

STATE_VERSION = 1
CAPTCHA_PHRASES = (
    "verify you are human", "access denied", "checking your browser",
    "unusual traffic", "captcha required", "cloudflare ray id",
)
MAX_SEEN = 10000
MAX_ITEMS = 500
HEALTH_CHECKPOINT_SECONDS = 900
DISCOVERY_MAX_BYTES = 8 * 1024 * 1024
_LIVE_HEALTH: dict[str, dict] = {}

# 빠른 경로는 단조 시계를 사용하고 교체 러너용 대기 만료 시각은 state에 저장한다.
_SITE_BLOCKED_UNTIL: dict[str, float] = {}
_TRAFFIC = ContextVar("storefront_traffic", default=None)
DEFAULT_INTERVAL = 45
DEFAULT_DURATION = 21000
OPTIONAL_RECHECK = 900


class SiteAccessDenied(RuntimeError):
    """쇼핑몰에서 요청을 거절한 경우(상태 403/429). Discord 오류와 구분."""

    def __init__(self, url: str, status: int, retry_after: str = ""):
        self.status = status
        self.host = urlsplit(url).hostname or "unknown"
        self.delay = _block_backoff_seconds()
        try:
            value = str(retry_after).strip()
            seconds = int(value) if value.isascii() and value.isdigit() else (
                parsedate_to_datetime(value).timestamp() - time.time())
            self.delay = max(2, math.ceil(seconds))
        except (ValueError, TypeError, OverflowError, OSError):
            pass
        super().__init__(f"HTTP {status}: {self.host} 응답으로 사이트 조회 대기 ({self.delay}초)")


class CatalogNotFound(RuntimeError):
    def __init__(self, status: int):
        self.status = status
        super().__init__(f"HTTP {status}: 카테고리 주소가 존재하지 않습니다")


def _block_backoff_seconds() -> int:
    """403/429 뒤 도메인별 재시도 대기(기본 15분, 최소 1분, 최대 1시간)."""
    raw = os.getenv("SITE_BLOCK_BACKOFF_SECONDS", "900")
    try:
        return min(3600, max(60, int(raw)))
    except ValueError:
        return 900


class ScanDeadline(Exception):
    """종료 시각에 도달하여 미착수 요청을 다음 실행에 넘긴다."""


class SiteTraffic:
    """하나의 동기식 순회가 사용하는 요청 시작 간격, 표본, 작업 종료 시각."""

    def __init__(self, interval=DEFAULT_INTERVAL, *, clock=None, sleep=None, get=None):
        self.clock = clock or time.monotonic
        self.sleep = sleep or time.sleep
        self.get = get
        self.interval = interval
        rpm = int(os.getenv("SITE_REQUESTS_PER_MINUTE", "40"))
        if rpm <= 0:
            raise ValueError("SITE_REQUESTS_PER_MINUTE는 양수여야 합니다")
        self.floor = 60 / rpm
        self.round_size = max(1, math.floor(interval / self.floor))
        self.samples = deque(maxlen=40)
        self.last_start = -math.inf
        self.deadline = math.inf
        self.count = 0
        self.recovery = {}

    @property
    def gap(self):
        floor = self.floor
        if self.recovery.get("until", 0) > time.time():
            floor *= self.recovery["factor"]
        if len(self.samples) < 8:
            return floor
        ordered = sorted(self.samples)
        return max(floor, 1.25 * ordered[math.ceil(0.95 * len(ordered)) - 1])

    @property
    def cycle_interval(self):
        return max(self.interval, math.ceil(self.round_size * self.gap))

    def admit(self, url):
        host = urlsplit(url).hostname
        if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
            raise SiteAccessDenied(url, 429)
        start = max(self.clock(), self.last_start + self.gap)
        if start >= self.deadline:
            raise ScanDeadline()
        delay = start - self.clock()
        if delay > 0:
            self.sleep(delay)
        now = self.clock()
        if now >= self.deadline:
            raise ScanDeadline()
        self.last_start = now
        self.count += 1
        return now

    def timeout(self, requested):
        remaining = self.deadline - self.clock()
        if remaining <= 0:
            raise ScanDeadline()
        if isinstance(requested, tuple):
            return tuple(min(t, remaining) for t in requested)
        return min(requested, remaining)


def _site_status(url, status, headers):
    if status in (403, 429, 503):
        raise SiteAccessDenied(url, status, headers.get("Retry-After", ""))


def _site_get(getter, url, *, follow=True, timeout=25, budget=None, **kwargs):
    """공개 GET의 리다이렉트 각 단계도 같은 예산으로 계산한다."""
    traffic = _TRAFFIC.get()
    origin = urlsplit(url)
    for _ in range(5):
        if budget is not None and budget[0] <= 0:
            raise _BudgetExhausted()
        if traffic:
            started = traffic.admit(url)
        if budget is not None:
            budget[0] -= 1
        try:
            response = (traffic.get if traffic and traffic.get else getter)(
                url, timeout=traffic.timeout(timeout) if traffic else timeout,
                allow_redirects=False, **kwargs)
        finally:
            if traffic:
                traffic.samples.append(max(0, traffic.clock() - started))
        try:
            _site_status(url, response.status_code, response.headers)
            if not follow or response.status_code not in (301, 302, 303, 307, 308):
                return response
            new = absolute_url(url, response.headers.get("Location", ""))
            dest = urlsplit(new)
            if (not new or dest.scheme != origin.scheme or dest.port != origin.port or
                    dest.hostname.removeprefix("www.") != origin.hostname.removeprefix("www.")):
                raise ValueError("다른 출처 또는 잘못된 리다이렉트입니다")
            url = new
            kwargs.pop("params", None)
        except Exception:
            if hasattr(response, "close"):
                response.close()
            raise
        response.close()
    raise ValueError("사이트 리다이렉트 한도 초과")

# 판매 버튼은 반드시 상품 상세 영역 안에 있어야 한다. 전역 메뉴 및 추천상품 오탐 방지.
ADD_TO_CART = re.compile(r"\badd\s+to\s+(?:bag|cart)\b", re.I)
COMING_SOON = re.compile(r"\bcoming\s+soon\b", re.I)
SOLD_OUT = re.compile(r"\b(?:sold\s+out|out\s+of\s+stock|notify\s+me|currently\s+unavailable)\b", re.I)
RECOMMENDATION_HEADINGS = (
    "you might also like", "related products", "recommended for you",
    "similar products", "complete the look", "customers also bought",
    "more to explore", "you may also like", "others also bought",
)
AVAILABILITY_LABELS = {
    "available": "구매 가능 (Add to Bag)",
    "coming_soon": "판매 대기 (Coming Soon)",
    "sold_out": "품절 (Sold Out)",
    "unknown": "확인 불가",
    "listed": "상품 등록됨 (구매 가능 미확인)",
    "selection_required": "옵션 선택/추가 확인 필요",
    "restricted": "현재 조회 환경에서 구매 제한",
    "unavailable": "현재 판매 불가",
}

# 크롬하츠 상품 URL: /<카테고리>/<슬러그>/<PID>.html  (예: /scents/22-eau-de-parfum/162006CRYXXX271.html)
#                    /<슬러그>/<PID>.html              (예: /black-sweatpants/190372BLKLRG01W.html)
PRODUCT_PATH = re.compile(r"/(\d{5,}[A-Za-z0-9_]{1,})\.html$")
PRICE = re.compile(r"[$€£¥₩]\s?\d[\d,]*(?:\.\d+)?")
STATUS_WORDS = re.compile(
    r"\b(?:sold\s+out|out\s+of\s+stock|notify\s+me|currently\s+unavailable|coming\s+soon)\b", re.I)
REGION_BLOCK = re.compile(r"not\s+available\s+in\s+your\s+country", re.I)
LOAD_MORE = re.compile(r"more\s+results|load\s+more|show\s+more|view\s+more", re.I)
# 브라우저 안에서 상품 링크 수를 세는 JS (PRODUCT_PATH와 동일 규칙)
JS_PRODUCT_LINK_SOURCE = r"\d{5,}[A-Za-z0-9_]{1,}\.html(?:[?#]|$)"
JS_PRODUCT_LINK_COUNT = (
    "() => [...document.querySelectorAll('a[href]')]"
    ".filter(a => new RegExp(" + json.dumps(JS_PRODUCT_LINK_SOURCE) + ").test(a.getAttribute('href') || '')).length")


def normalized(value: object) -> str:
    return re.sub(r"\s+", " ", unicodedata.normalize("NFC", str(value or ""))).strip()


def safe_url(raw: str) -> str:
    """Http(s) only, no URL credentials (no cookies or private data in links)."""
    parts = urlsplit(raw)
    if parts.scheme not in ("https", "http") or not parts.hostname or parts.username or parts.password:
        raise ValueError(f"허용되지 않은 URL: {raw!r}")
    if parts.hostname.lower() in ("localhost", "127.0.0.1", "::1"):
        raise ValueError("로컬 주소는 감시 대상에 사용할 수 없습니다")
    return urlunsplit((parts.scheme, parts.netloc, parts.path, parts.query, ""))


def absolute_url(base: str, href: str) -> str:
    if not href or href.startswith(("javascript:", "data:", "mailto:")):
        return ""
    try:
        return safe_url(urljoin(base, href))
    except ValueError:
        return ""


def normalized_product_url(url: str) -> str:
    """UTM 추적 파라미터는 상품 고유 식별에 사용하지 않는다."""
    if not url:
        return ""
    parts = urlsplit(url)
    kept = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
            if not k.lower().startswith("utm_") and k.lower() not in
            {"fbclid", "gclid", "igshid", "ref", "source"}]
    return urlunsplit((parts.scheme.lower(), parts.netloc.lower(), parts.path.rstrip("/") or "/",
                       urlencode(sorted(kept)), ""))


def _get_url(node, selector: str, base_url: str) -> str:
    element = node if selector == "self" else node.select_one(selector or "a[href]")
    if element is None:
        return ""
    if element.has_attr("href"):
        return absolute_url(base_url, str(element.get("href") or ""))
    anchor = element.find("a", href=True)
    return absolute_url(base_url, anchor.get("href", "")) if anchor else ""


def extract_items(html: str, monitor: dict) -> list[dict]:
    """DOM 상품 카드의 링크/고유 ID로 식별. 가격이나 카드 순서 변경은 신규로 보지 않음."""
    soup = BeautifulSoup(html, "html.parser")
    for selector in monitor.get("exclude_selectors", []):
        for element in soup.select(selector):
            element.decompose()
    root_selector = monitor.get("item_selector", "")
    if not root_selector:
        raise ValueError("items 모드에 item_selector가 필요합니다")
    nodes = soup.select(root_selector)
    if len(nodes) > MAX_ITEMS * 10:
        raise ValueError("선택한 영역이 지나치게 넓습니다. item_selector를 좁히세요")

    out = []
    seen_in_page = set()
    for node in nodes[:int(monitor.get("max_items", MAX_ITEMS))]:
        tsel = monitor.get("title_selector", "")
        title_node = node.select_one(tsel) if tsel and tsel != "self" else node
        title = normalized(title_node.get_text(" ", strip=True)) if title_node else ""
        if not title:
            continue
        url = _get_url(node, monitor.get("link_selector", "a[href]"), monitor["url"])
        id_attr = monitor.get("id_attribute", "")
        original_id = normalized(node.get(id_attr)) if id_attr else ""
        if original_id:
            base_key = "id:" + original_id
        elif url:
            base_key = "url:" + normalized_product_url(url)
        else:
            base_key = "title:" + title.casefold()
        key = hashlib.sha256(base_key.encode("utf-8")).hexdigest()[:32]
        if key in seen_in_page:
            continue
        seen_in_page.add(key)

        psel = monitor.get("price_selector", "")
        price_node = node.select_one(psel) if psel else None
        price = normalized(price_node.get_text(" ", strip=True)) if price_node else ""
        isel = monitor.get("image_selector", "")
        image_node = node.select_one(isel) if isel else None
        image = ""
        if image_node:
            src = image_node.get("src") or image_node.get("data-src") or ""
            if not src and image_node.get("srcset"):
                src = str(image_node.get("srcset")).split(",")[0].split(" ")[0]
            image = absolute_url(monitor["url"], str(src)) if src else ""
        out.append({"key": key, "title": title[:260], "url": url,
                    "price": price[:80], "image": image})
    return out


def extract_regions(html: str, monitor: dict) -> list[str]:
    soup = BeautifulSoup(html, "html.parser")
    for selector in monitor.get("exclude_selectors", []):
        for element in soup.select(selector):
            element.decompose()
    results = []
    for selector in monitor.get("region_selectors", []):
        elements = soup.select(selector)
        if not elements:
            raise ValueError(f"페이지 영역을 찾지 못했습니다: {selector}")
        parts = [normalized(e.get_text(" ", strip=True)) for e in elements]
        # 링크의 표시 문구가 같아도 목적지가 바뀌면 감지한다.
        for attr in monitor.get("region_attributes", ["href"]):
            for element in elements:
                nodes = [element, *element.find_all(attrs={attr: True})]
                for node in nodes:
                    value = str(node.get(attr, ""))
                    if value and attr == "href":
                        value = absolute_url(monitor["url"], value)
                    if value:
                        parts.append(f"{attr}={value}")
        value = normalized(" ".join(dict.fromkeys(parts)))
        if len(value) < int(monitor.get("minimum_text_length", 3)):
            raise ValueError(f"영역이 비어 있거나 너무 짧습니다: {selector}")
        results.append(value[:20000])
    if not results:
        raise ValueError("region 모드에는 region_selectors가 필요합니다")
    return results


def product_pid(base_url: str, href: str) -> tuple[str, str]:
    """상품 링크이면 (PID 대문자, 절대 URL), 아니면 ("", ""). 다른 도메인 링크는 제외."""
    url = absolute_url(base_url, href)
    if not url:
        return "", ""
    host = (urlsplit(url).hostname or "").removeprefix("www.")
    base_host = (urlsplit(base_url).hostname or "").removeprefix("www.")
    if host != base_host:
        return "", ""
    match = PRODUCT_PATH.search(urlsplit(url).path)
    return (match.group(1).upper(), url) if match else ("", "")


def _title_from_slug(url: str) -> str:
    parts = [p for p in urlsplit(url).path.split("/") if p]
    slug = parts[-2] if len(parts) >= 2 else ""
    return normalized(slug.replace("-", " ")).title()


def _clean_title(text: str) -> str:
    text = PRICE.sub(" ", text)
    text = STATUS_WORDS.sub(" ", text)
    return normalized(text)


def _visible_text(node) -> str:
    """숨김 처리된 요소의 문구는 제외하고 보이는 텍스트만 합친다."""
    chunks = []
    for s in node.find_all(string=True):
        if s.parent is not None and s.parent.name in ("script", "style", "noscript", "template"):
            continue
        if not _visible_enough(s.parent):
            continue
        chunks.append(str(s))
    return normalized(" ".join(chunks))


def _tile_status(text: str) -> str:
    if COMING_SOON.search(text):
        return "coming_soon"
    if SOLD_OUT.search(text):
        return "sold_out"
    return "listed"


def extract_catalog(html: str, monitor: dict) -> list[dict]:
    """카테고리 목록에서 상품 링크(PID 포함 *.html)를 찾아 상품별 {pid,key,title,url,price,image,status} 반환.

    CSS 클래스명에 의존하지 않고 '상품 상세 링크 패턴'으로 상품을 식별하므로 사이트의
    마크업이 조금 바뀌어도 동작한다. 라벨이 없으면 등록됨(listed)으로만 판단한다.
    """
    soup = BeautifulSoup(html, "html.parser")
    for el in soup.select("script, style, noscript, template, nav, header, footer"):
        el.decompose()
    for selector in monitor.get("exclude_selectors", []):
        for element in soup.select(selector):
            element.decompose()

    anchors: list[tuple[object, str, str]] = []
    pid_by_anchor: dict[int, str] = {}
    for a in soup.find_all("a", href=True):
        pid, url = product_pid(monitor["url"], str(a.get("href")))
        if pid:
            anchors.append((a, pid, url))
            pid_by_anchor[id(a)] = pid

    by_pid: dict[str, list[tuple[object, str]]] = {}
    for a, pid, url in anchors:
        by_pid.setdefault(pid, []).append((a, url))

    max_items = int(monitor.get("max_items", MAX_ITEMS))
    out = []
    for pid, links in list(by_pid.items())[:max_items]:
        first_anchor, url = links[0]
        # 같은 PID 링크만 포함하는 가장 큰 조상 = 상품 타일 (단, 텍스트가 너무 길어지면 중단)
        tile = first_anchor
        for _ in range(5):
            parent = tile.parent
            if parent is None or getattr(parent, "name", "") in ("body", "html", "[document]"):
                break
            pids = {pid_by_anchor[id(x)] for x in parent.find_all("a", href=True) if id(x) in pid_by_anchor}
            if len(pids) > 1 or len(normalized(parent.get_text(" ", strip=True))) > 700:
                break
            tile = parent

        text = _visible_text(tile)
        title = ""
        tsel = monitor.get("title_selector", "")
        candidates = [tile.select_one(tsel)] if tsel else []
        candidates += tile.select(".product-name, .pdp-link, .tile-name, h2, h3, h4, h5")
        for el in candidates:
            if el is not None:
                title = _clean_title(el.get_text(" ", strip=True))
                if title:
                    break
        if not title:
            for a, _u in links:
                title = _clean_title(a.get_text(" ", strip=True))
                if title:
                    break
        if not title:
            img = tile.find("img", alt=True)
            title = _clean_title(str(img.get("alt"))) if img else ""
        if not title:
            title = _title_from_slug(url) or pid

        price_match = PRICE.search(text)
        image = ""
        img = tile.find("img")
        if img is not None:
            src = img.get("src") or img.get("data-src") or ""
            if not src and img.get("srcset"):
                src = str(img.get("srcset")).split(",")[0].split(" ")[0]
            image = absolute_url(monitor["url"], str(src)) if src else ""

        out.append({"key": hashlib.sha256(("pid:" + pid).encode("utf-8")).hexdigest()[:32],
                    "pid": pid, "title": title[:260], "url": normalized_product_url(url),
                    "price": price_match.group(0)[:40] if price_match else "",
                    "image": image, "status": _tile_status(text)})
    return out


def _visible_enough(node) -> bool:
    """명백히 숨긴 버튼/요소를 무시. 브라우저 렌더링 후 추출한 HTML에서도 사용."""
    cursor = node
    for _ in range(40):
        if cursor is None or not hasattr(cursor, "attrs"):
            break
        if cursor.has_attr("hidden") or cursor.get("aria-hidden") == "true":
            return False
        if cursor.get("data-pagewatch-visible") != "1" and set(cursor.get("class", [])) & {
                "d-none", "hidden", "invisible", "sr-only", "visually-hidden"}:
            return False
        style = re.sub(r"\s+", "", str(cursor.get("style", "")).lower())
        if "display:none" in style or "visibility:hidden" in style:
            return False
        if cursor.get("data-pagewatch-visible") == "0":
            return False
        cursor = cursor.parent
    return True


def _disabled(node) -> bool:
    for el in [node, *list(node.parents)[:8]]:
        if el.has_attr("disabled") or str(el.get("aria-disabled", "")).lower() == "true":
            return True
        if "disabled" in el.get("class", []):
            return True
    return False


def _status_in_panel(panel) -> tuple[str, str] | None:
    """상품 헤더 가까이에 위치한 CTA 위주로 판단. 본문 및 다른 상품은 제외."""
    controls = panel.select("button, [role='button'], input[type='submit'], input[type='button']")
    labels = []
    enabled_add = False
    for el in controls:
        if not _visible_enough(el):
            continue
        label = normalized(el.get("value", "") if el.name == "input" else _visible_text(el))
        if not label:
            label = normalized(el.get("aria-label", ""))
        if label:
            labels.append(label)
            if ADD_TO_CART.search(label) and not _disabled(el):
                enabled_add = True
    # 실제 'Coming Soon' 버튼/표시가 있으면 이를 우선한다.
    for label in labels:
        if COMING_SOON.search(label):
            return "coming_soon", f"버튼: {label[:90]}"
    # 버튼이 아니라 출고 날짜 문구가 표시되는 경우도 있다.
    # 여기서는 'Coming Soon' 텍스트가 페이지 상세 영역에 실제 표시되어야 한다.
    for el in panel.find_all(["span", "p", "div", "strong", "label"], limit=90):
        if not _visible_enough(el):
            continue
        if len(el.find_all(["span", "p", "div", "strong", "label"])) > 8:
            continue
        value = _visible_text(el)
        if len(value) <= 90 and COMING_SOON.search(value):
            return "coming_soon", f"표시: {value[:90]}"
    for label in labels:
        if SOLD_OUT.search(label):
            return "sold_out", f"버튼: {label[:90]}"
    if enabled_add:
        return "available", "활성화된 Add to Bag/Cart 버튼"
    # 판매 버튼은 숨긴 템플릿/관련 상품 때문에 전체 body를 검색하지 않는다.
    for el in panel.find_all(["span", "p", "strong"], limit=90):
        if not _visible_enough(el):
            continue
        value = _visible_text(el)
        if len(value) <= 90 and SOLD_OUT.search(value):
            return "sold_out", f"표시: {value[:90]}"
    if any(ADD_TO_CART.search(label) for label in labels):
        return "selection_required", "구매 버튼 비활성: 옵션 선택 여부를 추가 확인해야 함"
    return None


def detect_availability(html: str, monitor: dict) -> dict:
    """크롬하츠 개별 상품 상세에서 재고/판매 CTA(Add to Bag 등)를 분류. 모르면 실패로 처리한다.

    브라우저 방문 성공/상품 설명 유무만으로 '판매 중'이라고 단정하지 않는다.
    사이트가 구조를 바꾸었으면 unknown 대신 예외를 내서 과거 정상 상태를 보존한다.
    """
    page_title = ""
    title_tag = BeautifulSoup(html, "html.parser").find("title")
    if title_tag is not None:
        page_title = normalized(title_tag.get_text(" ", strip=True))
    soup = BeautifulSoup(html, "html.parser")
    for el in soup.select("script, style, noscript, template, nav, header, footer"):
        el.decompose()
    h1 = soup.select_one("main h1") or soup.select_one("h1")
    if h1 is None:
        raise ValueError("상품 제목 h1을 찾지 못했습니다. 차단 또는 페이지 구조 변경 가능성")
    title = normalized(h1.get_text(" ", strip=True))
    # 크롬하츠는 h1에 '+22+' 같은 접두어가 빠지고 <title>에만 들어 있으므로 둘 다 확인한다.
    expected_title = normalized(monitor.get("expected_title_contains", ""))
    if expected_title and expected_title.casefold() not in (title + " | " + page_title).casefold():
        raise ValueError(f"다른 상품 페이지로 이동했습니다. 실제 제목: {title[:100]}")
    # 크롬하츠 상품 페이지에는 'SKU' 문구가 없고 상품코드(PID)가 URL/이미지 파일명에 들어 있다.
    sku = normalized(monitor.get("expected_pid") or monitor.get("expected_sku", ""))
    if sku and sku.casefold() not in html.casefold():
        raise ValueError(f"정확한 상품코드 {sku}를 확인하지 못했습니다. 차단/다른 상품/구조 변경 가능성")
    if REGION_BLOCK.search(_visible_text(soup)):
        return {"status": "restricted", "title": title[:200], "sku": sku,
                "url": monitor["url"], "evidence": "화면에 표시된 국가 제한 안내"}

    # h1이 포함된 최소 조상부터 탐색해서 첫 번째로 발견되는 구매 UI를 사용.
    # body/html까지 올라가면 헤더 'Coming Soon'이나 추천상품 CTA가 섞일 수 있어 제외.
    panel = h1.parent
    for _ in range(10):
        if panel is None or getattr(panel, "name", "") in ("body", "html"):
            break
        # 다른 주요 상품 타이틀까지 포함하는 지나치게 큰 영역은 건너뛴다.
        has_recommendations = any(
            normalized(h.get_text(" ", strip=True)).casefold().startswith(RECOMMENDATION_HEADINGS)
            for h in panel.select("h2, h3, h4")
        )
        if len(panel.select("h1")) == 1 and not has_recommendations:
            panel_text = normalized(panel.get_text(" ", strip=True))
            if len(panel_text) <= int(monitor.get("max_panel_chars", 6000)):
                finding = _status_in_panel(panel)
                if finding:
                    status, evidence = finding
                    return {"status": status, "title": title[:200], "sku": sku,
                            "url": monitor["url"], "evidence": evidence}
        panel = panel.parent
    raise ValueError("구매 상태가 불명확합니다. Coming Soon/Add to Cart/품절 신호를 찾지 못했습니다")


def validate_monitor(m: dict) -> None:
    if not isinstance(m, dict) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", str(m.get("id", ""))):
        raise ValueError("monitor id는 영문/숫자/_/- 문자 1~64자로 지정하세요")
    m["url"] = safe_url(str(m.get("url", "")))
    if m.get("mode", "items") not in ("items", "region", "availability", "catalog", "discovery"):
        raise ValueError(f"{m['id']}: mode는 catalog, discovery, availability, items 또는 region")
    if m.get("render", "http") not in ("http", "auto", "browser"):
        raise ValueError(f"{m['id']}: render는 http, auto 또는 browser")
    if m.get("mode", "items") == "items" and not m.get("item_selector"):
        raise ValueError(f"{m['id']}: item_selector를 지정하세요")
    if m.get("mode") == "region" and not m.get("region_selectors"):
        raise ValueError(f"{m['id']}: region_selectors를 지정하세요")
    if m.get("mode") == "availability":
        pid = str(m.get("expected_pid") or m.get("expected_sku") or "")
        if not re.fullmatch(r"[A-Za-z0-9]{6,30}", pid):
            raise ValueError("availability에는 상품코드 expected_pid(예: 162008CRYXXX271)가 필요합니다")
        if pid.casefold() not in m["url"].casefold():
            raise ValueError(f"{m['id']}: expected_pid {pid}가 url에 포함되어 있지 않습니다")
        if not m.get("expected_title_contains"):
            raise ValueError("availability에는 expected_title_contains가 필요합니다")
    if m.get("mode") == "catalog" and PRODUCT_PATH.search(urlsplit(m["url"]).path):
        raise ValueError(f"{m['id']}: catalog 모드에는 카테고리 목록 URL을 지정하세요(상품 상세 URL은 availability)")
    if not 1 <= int(m.get("max_items", MAX_ITEMS)) <= MAX_ITEMS:
        raise ValueError("max_items 범위: 1~500")


def _expand_load_more(page, m: dict) -> int:
    """'More Results' 류 버튼을 더 이상 상품이 늘지 않을 때까지 눌러 전체 목록을 펼친다."""
    clicks = 0
    m["_catalog_complete"] = False
    for _ in range(int(m.get("max_load_more", 8))):
        try:
            button = page.locator("button, a, [role=button]").filter(has_text=LOAD_MORE).first
            if button.count() == 0:
                m["_catalog_complete"] = True
                break
            if not button.is_visible():
                m["_catalog_complete"] = not button.get_attribute("data-url")
                break
            before = page.evaluate("(" + JS_PRODUCT_LINK_COUNT + ")()")
            button.scroll_into_view_if_needed(timeout=3000)
            button.click(timeout=5000)
            clicks += 1
            page.wait_for_function(
                "([src, n]) => [...document.querySelectorAll('a[href]')]"
                ".filter(a => new RegExp(src).test(a.getAttribute('href') || '')).length > n",
                arg=[JS_PRODUCT_LINK_SOURCE, before], timeout=8000)
            page.wait_for_timeout(400)
        except Exception:
            # 실패/시간 초과를 목록 끝으로 단정하지 않는다. 누락 판정은 생략한다.
            break
    return clicks


def _mark_visibility(page, mode: str) -> None:
    """CSS로 실제 감춰진 버튼/상태 문구는 판단에 쓰지 않도록 표시한다."""
    if mode == "availability":
        page.evaluate("""() => {
          for (const el of document.querySelectorAll('button, [role=button], input[type=submit], input[type=button], span, p, div, strong, label')) {
            const css = getComputedStyle(el);
            const visible = css.display !== 'none' && css.visibility !== 'hidden' && el.getClientRects().length > 0;
            el.setAttribute('data-pagewatch-visible', visible ? '1' : '0');
          }
        }""")
    elif mode == "catalog":
        page.evaluate("""() => {
          const words = /sold\\s*out|out\\s*of\\s*stock|notify\\s*me|unavailable|coming\\s*soon/i;
          for (const el of document.querySelectorAll('body *')) {
            if (el.children.length > 0 || !words.test(el.textContent || '')) continue;
            const css = getComputedStyle(el);
            const visible = css.display !== 'none' && css.visibility !== 'hidden' && el.getClientRects().length > 0;
            el.setAttribute('data-pagewatch-visible', visible ? '1' : '0');
          }
        }""")


def _catalog_pages(soup, m, headers):
    """SFRA가 게시한 다음 조각만 읽는다. 숨겨진 스크롤 버튼도 실제 다음 페이지다."""
    base = m["_final_url"]
    origin = urlsplit(base)
    footer = soup.select_one(".grid-footer")
    category = footer.select_one("input.category-id") if footer else None
    cgid = category.get("value") if category else None
    seen_pids = {product_pid(base, a["href"])[0] for a in soup.select(".product-tile a[href]")}
    position = 0
    pages = 0
    m["_catalog_complete"] = False
    while footer:
        button = footer.select_one(".show-more [data-url], #showMore[data-url]")
        if not button:
            break
        url = absolute_url(base, str(button.get("data-url", "")))
        dest = urlsplit(url)
        query = dict(parse_qsl(dest.query))
        offset = query.get("start", "")
        if (dest[:2] != origin[:2] or not dest.path.endswith("/Search-UpdateGrid")
                or not cgid or query.get("cgid") != cgid or not re.fullmatch(r"[0-9]{1,8}", offset)
                or int(offset) <= position or pages >= int(m.get("max_load_more", 8))):
            print(f"[PARTIAL] {m['url']} 다음 목록 주소/페이지 한도 확인 필요", file=sys.stderr)
            return str(soup)
        response = _site_get(requests.get, url, params={"selectedUrl": url},
                             headers=dict(headers, Referer=base, **{"X-Requested-With": "XMLHttpRequest"}))
        response.raise_for_status()
        fragment = BeautifulSoup(response.text, "html.parser")
        next_footer = fragment.select_one(".grid-footer")
        marker = next_footer.select_one("input.category-id") if next_footer else None
        received = {pid for a in fragment.select(".product-tile a[href]")
                    if (pid := product_pid(base, a["href"])[0])}
        if (fragment.find("html") or marker is None or marker.get("value") != cgid
                or not received.difference(seen_pids)):
            raise ValueError("다음 상품 목록 조각을 검증하지 못했습니다")
        seen_pids.update(received)
        # 사이트의 search.js와 같은 위치에 조각을 합쳐 메뉴·발견 링크도 유지한다.
        footer.replace_with(fragment)
        footer = next_footer
        position = int(offset)
        pages += 1
    unresolved = any(LOAD_MORE.search(el.get_text(" ", strip=True))
                     for el in soup.select("button, a, [role=button]"))
    m["_catalog_complete"] = not unresolved and len(seen_pids) <= int(m.get("max_items", MAX_ITEMS))
    if unresolved:
        print(f"[PARTIAL] {m['url']} 남은 페이지를 확인할 수 없습니다", file=sys.stderr)
    return str(soup)


def _pace_browser(context, traffic, base):
    """대체 렌더링의 같은 출처 GET도 순차 처리한다. 리다이렉트를 숨겨서 보내지 않는다."""
    outcome = {"error": None, "document_url": base}
    origin = urlsplit(base)[:2]

    def route_request(route):
        request = route.request
        url = request.url
        if (outcome["error"] or request.method != "GET" or urlsplit(url)[:2] != origin
                or request.resource_type in ("image", "media", "font")):
            route.abort()
            return
        try:
            for _ in range(5):
                started = traffic.admit(url)
                try:
                    response = route.fetch(url=url, max_redirects=0, max_retries=0,
                                           timeout=max(1, int(1000 * traffic.timeout(25))))
                finally:
                    traffic.samples.append(max(0, traffic.clock() - started))
                try:
                    headers = {k.title(): v for k, v in response.headers.items()}
                    _site_status(url, response.status, headers)
                    if response.status not in (301, 302, 303, 307, 308):
                        if outcome["error"]:
                            route.abort()
                            return
                        if request.is_navigation_request() and request.url == base:
                            outcome["document_url"] = url
                        route.fulfill(response=response)
                        return
                    url = absolute_url(url, headers.get("Location", ""))
                    if urlsplit(url)[:2] != origin:
                        raise ValueError("브라우저 요청이 다른 출처로 이동했습니다")
                finally:
                    response.dispose()
            raise ValueError("브라우저 리다이렉트 한도 초과")
        except Exception as exc:
            old = outcome["error"]
            if old is None or (isinstance(exc, SiteAccessDenied) and exc.delay > getattr(old, "delay", 0)):
                outcome["error"] = exc
            route.abort()

    context.route("**/*", route_request)
    return outcome


def fetch_html(m: dict, browser=None) -> str:
    url = m["url"]
    render = m.get("render", "http")
    mode = m.get("mode", "items")
    if render in ("http", "auto"):
        headers = {"User-Agent": "PageWatch/1.0 (read-only personal monitor)"}
        resp = _site_get(requests.get, url, headers=headers)
        if resp.status_code in (404, 410) and m.get("optional_catalog"):
            raise CatalogNotFound(resp.status_code)
        resp.raise_for_status()
        m["_final_url"] = safe_url(resp.url)
        html = resp.text
        soup = BeautifulSoup(html, "html.parser")
        if any(p in soup.get_text(" ", strip=True).lower()[:3000] for p in CAPTCHA_PHRASES):
            raise SiteAccessDenied(url, resp.status_code)
        if mode == "catalog":
            html = _catalog_pages(soup, m, headers)
        if render == "auto":
            path = urlsplit(m["_final_url"]).path
            if mode == "discovery":
                needs_browser = not any(discovery_url(url, a["href"])[1] == "category"
                                        for a in soup.select("header .b-dropdown-menu a[href], nav a[href]"))
            else:
                links = soup.select("main a[href], .product-grid a[href]")
                needs_browser = (mode == "catalog" and path.rstrip("/") and not PRODUCT_PATH.search(path)
                                 and not any(product_pid(url, a["href"])[0] or discovery_url(url, a["href"])[1]
                                             for a in links))
            if needs_browser:
                render = "browser"
    if render == "browser":
        if browser is None:
            raise RuntimeError("browser 감시에 Playwright Chromium이 필요합니다")
        if callable(browser):
            browser = browser()
        context = browser.new_context(locale="en-US", viewport={"width": 1440, "height": 900},
                                      service_workers="block")
        outcome = {}
        try:
            page = context.new_page()
            traffic = _TRAFFIC.get()
            if traffic:
                outcome = _pace_browser(context, traffic, m.get("_final_url", url))
            response = page.goto(m.get("_final_url", url), wait_until="domcontentloaded", timeout=35000)
            if response is not None:
                _site_status(url, response.status, {k.title(): v for k, v in response.headers.items()})
            if response is not None and response.status in (404, 410) and m.get("optional_catalog"):
                raise CatalogNotFound(response.status)
            if response is not None and response.status >= 400:
                raise RuntimeError(f"HTTP {response.status}")
            m["_final_url"] = safe_url(outcome.get("document_url", page.url))
            mode = m.get("mode", "items")
            if mode == "discovery":
                # 메뉴 토글만 연다. 실제 상품/장바구니 링크는 클릭하지 않는다.
                shop = page.locator("button, [role=button], a").filter(
                    has_text=re.compile(r"^\s*shop\s*$", re.I)).first
                if shop.count() and shop.is_visible():
                    href = shop.get_attribute("href") or ""
                    if not href or href.startswith(("#", "javascript:")):
                        shop.click(timeout=3000)
            inactive = m.get("optional_catalog") and urlsplit(m["_final_url"]).path.rstrip("/") == ""
            direct_product = bool(PRODUCT_PATH.search(urlsplit(m["_final_url"]).path))
            selector = m.get("wait_selector") or (m.get("item_selector") if mode == "items"
                           else "h1" if mode == "availability"
                           else "" if mode == "catalog"
                           else m.get("region_selectors", [""])[0])
            if mode == "catalog" and not selector and not inactive and not direct_product and not m.get("optional_catalog"):
                # 상품 상세 링크(PID.html)가 DOM에 나타날 때까지 대기
                page.wait_for_function("() => (" + JS_PRODUCT_LINK_COUNT + ")() > 0", timeout=20000)
            elif selector and not inactive:
                page.locator(selector).first.wait_for(state="visible", timeout=20000)
            page.wait_for_timeout(min(int(m.get("settle_ms", 1200)), 5000))
            if mode == "catalog" and not inactive and not direct_product:
                _expand_load_more(page, m)
            elif mode == "catalog":
                m["_catalog_complete"] = False
            _mark_visibility(page, mode)
            html = page.content()
            if outcome.get("error"):
                raise outcome["error"]
            if mode == "catalog" and not m.get("_catalog_complete") and not inactive and not direct_product:
                rendered = BeautifulSoup(html, "html.parser")
                if rendered.select_one(".grid-footer .show-more [data-url]"):
                    html = _catalog_pages(rendered, m, {"User-Agent": "PageWatch/1.0 (read-only personal monitor)"})
        finally:
            context.close()
            if outcome.get("error"):
                raise outcome["error"]
    plain = BeautifulSoup(html, "html.parser").get_text(" ", strip=True).lower()
    if any(phrase in plain[:3000] for phrase in CAPTCHA_PHRASES):
        raise SiteAccessDenied(url, 200)
    return html


def load_state(path: Path) -> dict:
    if not path.exists():
        return {"version": STATE_VERSION, "monitors": {}}
    state = json.loads(path.read_text(encoding="utf-8"))
    if state.get("version") != STATE_VERSION or not isinstance(state.get("monitors"), dict):
        raise ValueError("알 수 없는 상태 파일 형식 — 백업 후 수동 확인하세요")
    return state


def save_state(path: Path, state: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def _when() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


DISCOVERY_EXCLUDE = {"account", "cart", "checkout", "contact", "contact-us", "customer-service", "disclosure",
                     "locations", "login", "logout", "magazine", "order-status", "privacy",
                     "stores", "wishlist", "general", "terms", "register", "api"}


def discovery_url(base: str, raw: str) -> tuple[str, str, str]:
    """다단계/HTML 카테고리와 cgid 링크를 허용하되 조회 동작/파일/외부 링크는 구분한다."""
    url = absolute_url(base, raw)
    if not url:
        return "", "", "invalid_url"
    parts, origin = urlsplit(url), urlsplit(base)
    if (parts.hostname or "").removeprefix("www.") != (origin.hostname or "").removeprefix("www."):
        return "", "", "external_host"
    try:
        port = parts.port
    except ValueError:
        return "", "", "unsupported_port"
    if port not in (None, 80, 443):
        return "", "", "unsupported_port"
    path = parts.path.rstrip("/") or "/"
    segments = unquote(path).lower().strip("/").split("/")
    if any(s.removesuffix(".html").removesuffix(".htm") in DISCOVERY_EXCLUDE
           or re.match(r"^(cart|checkout|account|login|logout)[-.]", s)
           for s in segments):
        return "", "", "non_catalog_path"
    # 실제 sitemap은 별칭이 없는 분류도 Search-Show?cgid=... 형태로 공개한다.
    controller = re.fullmatch(r"/on/demandware\.store/Sites-[\w-]+/[\w-]+/Search-Show", path)
    if controller:
        params = parse_qsl(parts.query, keep_blank_values=True)
        if len(params) == 1 and params[0][0] == "cgid" and re.fullmatch(r"[\w.-]{1,100}", params[0][1]):
            return urlunsplit((origin.scheme, origin.netloc, path, urlencode(params), "")), "category", ""
        return "", "", "unsupported_query"
    if "/on/demandware.store/" in path.lower():
        return "", "", "application_endpoint"
    kept = []
    for key, value in parse_qsl(parts.query, keep_blank_values=True):
        name = key.lower()
        if PRODUCT_PATH.search(path) and (re.fullmatch(r"dwvar_[a-z0-9_-]+", name)
                                          or (name == "quantity" and value == "1")):
            # 옵션 선택은 상품의 존재 식별과 분리한다. 실제 옵션 조회는 상세 감시가 담당한다.
            continue
        elif name == "cgid" and value:
            kept.append((name, value))
        elif name.startswith("utm_") or name in {
                "fbclid", "gclid", "igshid", "ref", "source", "start", "sz", "page", "sort", "srule"}:
            continue
        else:
            return "", "", "unsupported_query"
    if path == "/" and not kept:
        return "", "", "home"
    if "search" in segments and not kept:
        return "", "", "search_without_category"
    if not re.fullmatch(r"/[\w%~./-]+", path) or any(s in (".", "..") for s in segments):
        return "", "", "unsupported_path"
    if "." in segments[-1] and not segments[-1].endswith((".html", ".htm")):
        return "", "", "asset_or_document"
    canonical = urlunsplit((origin.scheme, origin.netloc, path, urlencode(sorted(set(kept))), ""))
    return canonical, "product" if PRODUCT_PATH.search(path) else "category", ""


def discovery_links(html: str, base: str):
    soup = BeautifulSoup(html, "html.parser")
    for el in soup.select("script, style, noscript, template"):
        el.decompose()
    for a in soup.select("a[href]"):
        raw = str(a.get("href", ""))
        title = normalized(a.get_text(" ", strip=True)) or (a.img.get("alt", "") if a.img else "")
        yield raw, str(title)[:260]

def extract_discovery(html: str, m: dict) -> list[dict]:
    found = {}
    for raw, title in discovery_links(html, m["url"]):
        url, _kind, _reason = discovery_url(m["url"], raw)
        if not url:
            continue
        key = hashlib.sha256(url.encode()).hexdigest()[:32]
        found[key] = {"key": key, "title": title or urlsplit(url).path, "url": url}
    return list(found.values())[:MAX_ITEMS]


def optional_catalog_products(html: str, m: dict) -> list[dict]:
    final = urlsplit(m.get("_final_url", m["url"]))
    original = urlsplit(m["url"])
    if (final.hostname or "").removeprefix("www.") != (original.hostname or "").removeprefix("www."):
        raise ValueError("다른 도메인으로 이동했습니다")
    if final.path.rstrip("/") == "":
        # 메인 이동은 품절/목록 삭제의 증거가 아니다(국가/접근 정책일 수도 있음).
        m["_catalog_complete"] = False
        return []
    pid, product_url = product_pid(m["url"], m.get("_final_url", m["url"]))
    if pid:
        try:
            details = detect_availability(html, dict(m, url=product_url))
            title, status = details["title"], details["status"]
        except ValueError:
            soup = BeautifulSoup(html, "html.parser")
            heading = soup.select_one("main h1") or soup.select_one("h1")
            if not heading:
                raise ValueError("상품 상세 제목을 찾지 못했습니다")
            title, status = normalized(heading.get_text(" ", strip=True)), "unknown"
        return [{"key": hashlib.sha256(("pid:" + pid).encode()).hexdigest()[:32],
                 "pid": pid, "title": title, "url": normalized_product_url(product_url),
                 "price": "", "image": "", "status": status}]
    products = extract_catalog(html, m)
    if not products:
        raise ValueError("메인이 아닌 페이지에서 상품을 찾지 못했습니다: 구조 변경 또는 렌더링 확인 필요")
    return products

def _age_seconds(stamp: str | None) -> float:
    try:
        return max(0.0, (datetime.now(timezone.utc) - datetime.fromisoformat(stamp or "")).total_seconds())
    except (ValueError, TypeError):
        return float("inf")


def _seen_stamp(old: dict, now: str, changed: bool = False) -> str:
    # 매분 무변경 확인만으로 Git 커밋이 생기지 않도록 15분 단위로 보존한다.
    if changed or _age_seconds(old.get("last_seen_at")) >= HEALTH_CHECKPOINT_SECONDS:
        return now
    return old["last_seen_at"]


class DiscoveryAudit:
    """관측한 페이지 + robots/sitemap + 후보 페이지를 제한된 예산으로 순회한다.

    URL 목록/재시도 시각/판정 사유를 state에 보존한다. 어디에도 공개되지 않은 URL의
    존재는 판단할 수 없으며, 크기/개수 제한과 조회 실패를 성공으로 숨기지 않는다.
    """

    def __init__(self, state: dict, monitor: dict, active: list[dict]):
        self.state, self.monitor, self.active = state, monitor, active
        self.base = monitor["url"]
        self.interval = max(60, int(monitor.get("discovery_interval_seconds", 900)))
        self.limit = min(MAX_SEEN, max(100, int(monitor.get("discovery_max_candidates", 2000))))
        self.max_monitors = max(len(active), min(200, int(monitor.get("discovery_max_monitors", 100))))
        self.data = state.setdefault("discovery_audit", {}).setdefault(monitor["id"], {
            "initialized": bool(state["monitors"].get(monitor["id"], {}).get("initialized")),
            "candidates": {}, "sources": {}, "excluded": {}, "history": [],
        })
        self.known = {self.canonical(m["url"]): m for m in active}
        self.limits_reported: set[str] = set()
        root = urlunsplit((*urlsplit(self.base)[:2], "/", "", ""))
        self.add_source(urljoin(root, "robots.txt"), "robots")
        for url in monitor.get("discovery_sitemap_urls", [urljoin(root, "sitemap.xml"),
                                                        urljoin(root, "sitemap_index.xml")]):
            self.add_source(url, "sitemap")
        for url in monitor.get("discovery_seed_urls", []):
            self.remember(url, "", self.base)
        # v1의 홈페이지 seen 목록도 그대로 이어받는다. 한 단계 경로 제한은 없다.
        for item in state["monitors"].get(monitor["id"], {}).get("seen", {}).values():
            self.remember(item["url"], item.get("title", ""), self.base)

    def canonical(self, url: str) -> str:
        return discovery_url(self.base, url)[0] or normalized_product_url(url)

    def log(self, code: str, url: str, reason: str, source: str = "") -> None:
        entry = {"code": code, "url": url[:2000], "reason": reason[:300], "source": source[:2000]}
        history = self.data["history"]
        for old in reversed(history):
            if all(old.get(k) == v for k, v in entry.items()):
                if _age_seconds(old.get("at")) < self.interval:
                    return
                break
        entry["at"] = _when()
        history.append(entry)
        del history[:-500]
        print("[DISCOVERY] " + json.dumps(entry, ensure_ascii=False), flush=True)

    def limit_notice(self, code: str, reason: str) -> None:
        if code not in self.limits_reported:
            self.limits_reported.add(code)
            self.log(code, self.base, reason)

    def exclude(self, raw: str, reason: str, source: str) -> None:
        if reason in ("home", "invalid_url"):
            return
        key = hashlib.sha256((raw + reason).encode()).hexdigest()[:32]
        excluded = self.data["excluded"]
        if key in excluded:
            return
        if len(excluded) >= 200:
            self.limit_notice("exclusion_log_limit", "제외 URL 상세 기록 200개 한도. 이후 제외 내역은 생략됩니다.")
            return
        excluded[key] = {"url": raw[:2000], "reason": reason, "source": source, "at": _when()}
        self.log("excluded", raw, reason, source)

    def remember(self, raw: str, title: str, source: str) -> None:
        absolute = absolute_url(source, raw)
        url, kind, reason = discovery_url(self.base, absolute)
        if not url:
            self.exclude(absolute or raw, reason, source)
            return
        candidates = self.data["candidates"]
        if url not in candidates:
            if len(candidates) >= self.limit:
                self.limit_notice("candidate_limit", f"후보 {self.limit}개 한도. 이후 URL을 등록하지 못했습니다. 설정/목록 검토 필요.")
                return
            candidates[url] = {"url": url, "title": title or (_title_from_slug(url) if kind == "product" else urlsplit(url).path),
                               "kind": kind, "status": "pending", "sources": [],
                               "first_seen_at": _when(), "last_checked_at": "",
                               "notify": self.data["initialized"] or self.monitor.get("notify_on_first_run", False)}
            self.log("candidate_found", url, kind, source)
        candidate = candidates[url]
        if source not in candidate["sources"] and len(candidate["sources"]) < 8:
            candidate["sources"].append(source)
        if title:
            candidate["title"] = title
        if url in self.known:
            candidate["status"] = ("monitoring" if self.known[url]["id"].startswith("discovered-")
                                   else "configured")
        elif kind == "product":
            # 상품 sitemap만 있는 경우 /category/slug/PID.html의 상위 분류도 검증한다.
            parent_parts = urlsplit(url).path.strip("/").split("/")[:-2]
            if parent_parts:
                parent = urlunsplit((*urlsplit(url)[:2], "/" + "/".join(parent_parts), "", ""))
                self.remember(parent, "", url)

    def register_products(self, record_events) -> None:
        # 기본 목록의 compare/_register_products가 끝난 뒤 처리하여 알림 중복을 막는다.
        for candidate in list(self.data["candidates"].values()):
            if candidate["kind"] != "product" or candidate["status"] != "pending":
                continue
            url, title = candidate["url"], candidate["title"]
            pid, _ = product_pid(self.base, url)
            key = (urlsplit(url).hostname or "") + ":" + pid
            product = {"pid": pid, "title": title or _title_from_slug(url), "url": url, "status": "listed"}
            events = []
            if key not in self.state.get("tracked_products", {}) and candidate["notify"]:
                events = [{"kind": "new_product", **product, "observed_at": _when()}]
            source_monitor = dict(self.monitor, _products=[product])
            _accept_observation(self.state, source_monitor, None, events, record_events)
            candidate["status"] = "tracked"
            self.log("product_registered", url, "상품 상세 감시 등록", candidate["sources"][0])

    def observe(self, html: str, source: str) -> None:
        for raw, title in discovery_links(html, source):
            self.remember(raw, title, source)

    def add_source(self, raw: str, kind: str, parent: str = "") -> None:
        url = absolute_url(parent or self.base, raw)
        if not url:
            self.exclude(raw, "invalid_sitemap", parent)
            return
        if (urlsplit(url).hostname or "").removeprefix("www.") != (urlsplit(self.base).hostname or "").removeprefix("www."):
            self.exclude(url, "external_sitemap_not_scanned", parent)
            return
        sources = self.data["sources"]
        if url not in sources:
            if len(sources) >= 100:
                self.limit_notice("source_limit", "robots/sitemap 100개 한도. 나머지 소스는 읽지 못했습니다.")
                return
            sources[url] = {"kind": kind, "last_attempt_at": "", "status": "pending"}

    def read_source(self, url: str) -> tuple[bytes, str]:
        """리다이렉트도 같은 호스트만 허용하고 압축 전후 크기를 제한한다."""
        for _ in range(4):
            with _site_get(requests.get, url, follow=False, timeout=(5, 15), stream=True,
                              headers={"User-Agent": "PageWatch/1.0 (read-only personal monitor)"}) as response:
                if response.status_code in (301, 302, 303, 307, 308):
                    next_url = absolute_url(url, response.headers.get("Location", ""))
                    if not next_url or (urlsplit(next_url).hostname or "").removeprefix("www.") != (urlsplit(self.base).hostname or "").removeprefix("www."):
                        raise ValueError("sitemap이 외부/알 수 없는 주소로 이동했습니다")
                    url = next_url
                    continue
                response.raise_for_status()
                payload = bytearray()
                started = time.monotonic()
                for chunk in response.iter_content(65536):
                    payload.extend(chunk)
                    if len(payload) > DISCOVERY_MAX_BYTES or time.monotonic() - started > 20:
                        raise ValueError("sitemap 크기/읽기 시간 한도 초과: 완전한 탐색이 아닙니다")
                data = bytes(payload)
                if data.startswith(b"\x1f\x8b"):
                    with gzip.GzipFile(fileobj=io.BytesIO(data)) as zipped:
                        data = zipped.read(DISCOVERY_MAX_BYTES + 1)
                if len(data) > DISCOVERY_MAX_BYTES:
                    raise ValueError("압축 해제 sitemap 크기 한도 초과: 완전한 탐색이 아닙니다")
                return data, url
        raise ValueError("sitemap 리다이렉트 한도 초과")

    def scan_source(self, url: str, info: dict) -> None:
        previous_attempt = info.get("last_attempt_at", "")
        info["last_attempt_at"] = _when()
        try:
            data, final_url = self.read_source(url)
            if info["kind"] == "robots":
                if b"<html" in data.lower() or b"<!doctype" in data.lower():
                    raise ValueError("robots.txt 대신 HTML 페이지가 반환되었습니다")
                for line in data.decode("utf-8-sig", errors="replace").splitlines():
                    match = re.match(r"\s*Sitemap\s*:\s*(\S+)", line, re.I)
                    if match:
                        self.add_source(match.group(1), "sitemap", final_url)
            else:
                if re.search(br"<!\s*(DOCTYPE|ENTITY)\b", data, re.I):
                    raise ValueError("외부 선언이 있는 XML은 읽지 않습니다")
                text = data.decode("utf-8-sig")
                if text.lstrip().startswith("<"):
                    root = ET.fromstring(text)
                    tag = root.tag.rsplit("}", 1)[-1]
                    if tag not in ("sitemapindex", "urlset"):
                        raise ValueError("sitemap XML이 아닙니다: " + tag)
                    for child in root:
                        loc = child.find("{*}loc")
                        if loc is None or not loc.text:
                            continue
                        if tag == "sitemapindex":
                            self.add_source(loc.text.strip(), "sitemap", final_url)
                        else:
                            self.remember(loc.text.strip(), "", final_url)
                else:
                    lines = [line.strip() for line in text.splitlines() if line.strip()]
                    if not lines or any(not line.startswith(("http://", "https://")) for line in lines):
                        raise ValueError("sitemap XML 또는 URL 목록이 아닙니다")
                    for line in lines:
                        self.remember(line, "", final_url)
            info.update(status="ok", last_success_at=_when(), error="")
            self.log("source_checked", url, info["kind"])
        except ScanDeadline:
            info["last_attempt_at"] = previous_attempt
            raise
        except Exception as exc:
            info.update(status="error", error=_error_text(exc))
            self.log("source_error", url, info["error"])
            if isinstance(exc, SiteAccessDenied):
                raise

    def dynamic_monitor(self, candidate: dict) -> dict:
        url = candidate["url"]
        parts = urlsplit(url)
        identity = parts.path.rstrip("/") + ("?" + parts.query if parts.query else "")
        render = candidate.get("render", "http")
        if render == "browser" and self.monitor.get("render") == "auto":
            render = "auto"
        return {"id": "discovered-" + hashlib.sha256(identity.encode()).hexdigest()[:16],
                "name": "자동 발견 " + identity, "url": url, "enabled": True,
                "mode": "catalog", "render": render, "optional_catalog": True,
                "settle_ms": 1500, "max_load_more": 8,
                "notify_on_first_run": candidate.get("notify", True),
                "notify_on_new": True, "notify_on_restock": True}

    def restore(self) -> None:
        for candidate in self.data["candidates"].values():
            if candidate["status"] != "monitoring" or candidate["url"] in self.known:
                continue
            if len(self.active) >= self.max_monitors:
                self.limit_notice("monitor_limit", "감시 대상 한도로 일부 자동 카테고리를 활성화하지 못했습니다")
                break
            dynamic = self.dynamic_monitor(candidate)
            validate_monitor(dynamic)
            self.active.append(dynamic)
            self.known[candidate["url"]] = dynamic

    def scan(self, browser, record_events, record_health) -> None:
        deadline = time.monotonic() + 25
        host = urlsplit(self.base).hostname or ""
        if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
            self.log("paused", self.base, "403/429 도메인 대기 중: 추가 탐색을 건너뜁니다")
            return
        sources = sorted(list(self.data["sources"].items()), key=lambda pair: pair[1]["last_attempt_at"])
        due = [(url, info) for url, info in sources if _age_seconds(info["last_attempt_at"]) >= self.interval]

        def scan_sources():
            for url, info in due[:2]:
                if time.monotonic() >= deadline:
                    break
                self.scan_source(url, info)

        # 느린 sitemap이 계속 예산을 소진해도 후보 검증이 굶지 않도록 순서를 교대한다.
        source_first = self.data.get("source_first", True)
        self.data["source_first"] = not source_first
        if source_first:
            scan_sources()
        pending = [c for c in self.data["candidates"].values()
                   if c["kind"] == "category" and c["status"] not in ("monitoring", "configured")
                   and _age_seconds(c["last_checked_at"]) >= self.interval]
        pending.sort(key=lambda c: c["last_checked_at"])
        for candidate in pending[:2]:
            if time.monotonic() >= deadline:
                break
            previous_check = candidate["last_checked_at"]
            candidate["last_checked_at"] = _when()
            candidate["render"] = "auto" if callable(browser) else "browser" if browser is not None else "http"
            dynamic = self.dynamic_monitor(candidate)
            started = time.monotonic()
            try:
                validate_monitor(dynamic)
                html = fetch_html(dynamic, browser)
                final = dynamic.get("_final_url", dynamic["url"])
                if (urlsplit(final).hostname or "").removeprefix("www.") != host.removeprefix("www."):
                    raise ValueError("후보 페이지가 다른 도메인으로 이동했습니다")
                # 상품이 없는 중간 분류 페이지도 자식 링크를 먼저 수집한다.
                self.observe(html, final)
                current, events = compare(dynamic, self.state["monitors"].get(dynamic["id"]), html)
                if not dynamic.get("_products"):
                    raise ValueError("상품 목록 미확인/메인 리다이렉트: 자동 등록 보류, 다음 탐색에서 재확인")
                if len(self.active) >= self.max_monitors:
                    raise ValueError("감시 대상 한도 초과: 발견한 카테고리 등록 보류")
                if candidate.get("notify"):
                    events.append({"kind": "health", "title": "새 카테고리 자동 감시 추가",
                                   "message": candidate["title"], "url": candidate["url"], "observed_at": _when()})
                _accept_observation(self.state, dynamic, current, events, record_events)
                self.active.append(dynamic)
                self.known[candidate["url"]] = dynamic
                candidate.update(status="monitoring", reason="상품 목록 확인 후 감시 등록")
                self.log("category_registered", candidate["url"], candidate["reason"], candidate["sources"][0])
                record_health(dynamic, time.monotonic() - started)
            except ScanDeadline:
                candidate["last_checked_at"] = previous_check
                raise
            except Exception as exc:
                if candidate["status"] == "monitoring":
                    self.log("monitor_health_error", candidate["url"], _error_text(exc))
                else:
                    candidate.update(status="needs_review", reason=_error_text(exc))
                    self.log("needs_review", candidate["url"], candidate["reason"], candidate["sources"][0])
                if isinstance(exc, SiteAccessDenied):
                    raise
        if not source_first:
            scan_sources()
        self.register_products(record_events)
        if not any(c["status"] == "pending" for c in self.data["candidates"].values()) and not any(
                s["status"] == "pending" for s in self.data["sources"].values()):
            self.data["initialized"] = True
        if _age_seconds(self.data.get("last_summary_at")) >= self.interval:
            counts = {}
            for c in self.data["candidates"].values():
                counts[c["status"]] = counts.get(c["status"], 0) + 1
            self.log("coverage", self.base, json.dumps(counts, ensure_ascii=False)
                     + f"; source_errors={sum(s['status'] == 'error' for s in self.data['sources'].values())}"
                     + "; 공개 링크/sitemap 범위만 확인. 미공개 URL의 누락 여부는 판단 불가.")
            self.data["last_summary_at"] = _when()


def compare(m: dict, previous: dict | None, html: str) -> tuple[dict, list[dict]]:
    """알림은 별도 영속 큐로 전달한다. 이전 v1 상태 파일을 그대로 읽을 수 있다."""
    mode = m.get("mode", "items")
    new = copy.deepcopy(previous or {})
    new["mode"] = mode
    boot = previous is None or previous.get("mode") != mode or not previous.get("initialized", False)
    alert_on_first = bool(m.get("notify_on_first_run", False))
    events = []
    now = _when()
    if mode in ("items", "discovery"):
        items = extract_discovery(html, m) if mode == "discovery" else extract_items(html, m)
        if not items and (mode == "discovery" or not bool(m.get("allow_empty", False))):
            raise ValueError("상품/링크가 0개입니다. CSS 선택자/캡차/로그인 여부를 확인하세요")
        saved = dict(previous.get("seen", {}) if previous and not boot else {})
        old_snapshot = (previous or {}).get("snapshot")
        snapshot = {i["key"]: {"title": i["title"], "url": i["url"]} for i in items}
        for item in items:
            key = item["key"]
            old = saved.get(key)
            if not boot or alert_on_first:
                if old is None:
                    events.append({"kind": "item", **item})
                elif mode == "discovery" and old_snapshot is not None:
                    if key not in old_snapshot:
                        events.append({"kind": "item_reappeared", **item})
                    elif old_snapshot[key]["title"] != item["title"]:
                        events.append({"kind": "link_changed", **item,
                                       "before": old_snapshot[key]["title"]})
            saved[key] = {"title": item["title"], "url": item["url"]}
        new["seen"] = dict(list(saved.items())[-MAX_SEEN:])
        new["snapshot"] = snapshot
        new["last_count"] = len(items)
        if mode == "discovery":
            m["_products"] = []
            for item in items:
                pid, url = product_pid(m["url"], item["url"])
                if pid:
                    m["_products"].append({**item, "pid": pid, "url": url, "status": "listed"})
    elif mode == "catalog":
        products = optional_catalog_products(html, m) if m.get("optional_catalog") else extract_catalog(html, m)
        m["_products"] = products
        if not products and not m.get("optional_catalog") and not bool(m.get("allow_empty", False)):
            raise ValueError("상품 링크가 0개입니다. 차단/캡차/페이지 구조 변경 여부를 확인하세요")
        saved = copy.deepcopy(previous.get("seen", {}) if previous and not boot else {})
        present = set()
        for product in products:
            key = product["key"]
            present.add(key)
            old = saved.get(key, {})
            old_status = old.get("status", "listed")
            reappeared = bool(old) and old.get("present") is False
            changed = product["status"] != old_status or reappeared or not old
            saved[key] = {"title": product["title"], "url": product["url"],
                          "status": product["status"], "present": True, "miss_count": 0,
                          "last_seen_at": _seen_stamp(old, now, changed)}
            if boot and not alert_on_first:
                continue
            if not old and m.get("notify_on_new", True):
                events.append({"kind": "new_product", **product})
            elif reappeared and m.get("notify_on_reappear", True):
                events.append({"kind": "reappeared", **product})
            elif product["status"] == "available" and old_status in ("sold_out", "coming_soon"):
                if m.get("notify_on_restock", True):
                    events.append({"kind": "restock", **product, "previous_status": old_status})
            elif product["status"] == "sold_out" and old_status != "sold_out":
                if m.get("notify_on_sold_out", False):
                    events.append({"kind": "sold_out", **product, "previous_status": old_status})
        # 완전하게 읽은 정상 목록에서 연속 두 번 누락되어야 사라짐으로 확정한다.
        # 0개/리다이렉트/더 보기 실패 등은 목록 완전성이 확인될 때에만 반영한다.
        if m.get("_catalog_complete", True):
            for key, old in saved.items():
                if key not in present:
                    misses = min(2, old.get("miss_count", 0) + 1)
                    old["miss_count"] = misses
                    if misses >= 2:
                        old["present"] = False
        new["seen"] = dict(list(saved.items())[-MAX_SEEN:])
        new["last_count"] = len(products)
    elif mode == "availability":
        result = detect_availability(html, m)
        status = result["status"]
        old_status = (previous or {}).get("last_known_status", (previous or {}).get("status"))
        new.update(status=status, title=result["title"], sku=result["sku"])
        if status not in ("unknown", "selection_required", "listed"):
            new["last_known_status"] = status
        if not boot or alert_on_first:
            if status == "available" and old_status != "available":
                events = [{"kind": "availability", **result, "previous_status": old_status}]
            elif status != "available" and m.get("notify_on_unavailable", False) and status != (previous or {}).get("status"):
                events = [{"kind": "availability", **result, "previous_status": old_status}]
        m["_products"] = [{"pid": result["sku"], "title": result["title"],
                           "url": m["url"], "status": status}]
    else:
        regions = extract_regions(html, m)
        old_regions = previous.get("regions", []) if previous and not boot else []
        new["regions"] = regions
        # 업그레이드 시 href를 처음 포함한 값은 기준선으로 저장한다.
        baseline = previous and previous.get("region_format", 1) < 2
        new["region_format"] = 2
        if (not boot or alert_on_first) and not baseline:
            for index, after in enumerate(regions):
                before = old_regions[index] if index < len(old_regions) else ""
                if before != after:
                    events.append({"kind": "region", "selector": m["region_selectors"][index],
                                   "before": before, "after": after})
    new["initialized"] = True
    if new != previous:
        new["updated_at"] = now
    for event in events:
        event["observed_at"] = now
    return new, events


def _discord_url() -> str:
    url = os.environ.get("DISCORD_WEBHOOK_URL", "").strip()
    p = urlsplit(url)
    if p.scheme != "https" or p.hostname not in ("discord.com", "discordapp.com") or not re.fullmatch(
        r"/api(?:/v\d+)?/webhooks/\d+/[A-Za-z0-9_-]+/?", p.path
    ) or p.query or p.fragment:
        raise ValueError("DISCORD_WEBHOOK_URL에 정상적인 Discord 웹훅 URL을 GitHub Secret으로 설정하세요")
    return url


def _discord_len(text: str) -> int:
    return len(text.encode("utf-16-le")) // 2


def _discord_parts(text: str, limit: int = 3800) -> list[str]:
    # 이벤트가 길어도 뒷부분을 버리지 않는다.
    result, current, size = [], [], 0
    for char in text:
        width = _discord_len(char)
        if size + width > limit:
            result.append("".join(current))
            current, size = [], 0
        current.append(char)
        size += width
    if current:
        result.append("".join(current))
    return result or [""]


def _event_description(e: dict) -> str:
    title = str(e.get("title", "")).replace("`", "′").replace("[", "［").replace("]", "］")
    kind = e["kind"]
    if kind in ("new_product", "reappeared", "restock", "sold_out"):
        head = {"new_product": "🆕 신상품 등록", "reappeared": "👀 상품 재등장 (재입고 여부 추가 확인)",
                "restock": "🔄 구매 가능", "sold_out": "⛔ 품절"}[kind]
        desc = f"• {head}: **{title}**\n상품코드: `{e['pid']}`"
        desc += "\n상태: " + AVAILABILITY_LABELS.get(e.get("status"), "확인 불가")
        if e.get("price"):
            desc += f"\n가격: {e['price']}"
    elif kind in ("item", "item_reappeared", "link_changed"):
        head = {"item": "새 링크", "item_reappeared": "링크 재등장", "link_changed": "메뉴 문구 변경"}[kind]
        desc = f"• {head}: **{title}**"
        if kind == "link_changed":
            desc += f"\n이전 문구: {e.get('before', '')}"
    elif kind in ("availability", "variant"):
        status = AVAILABILITY_LABELS.get(e.get("status"), "확인 불가")
        old = AVAILABILITY_LABELS.get(e.get("previous_status"), "최초 확인")
        desc = f"• **{title}**\n상품코드: `{e.get('pid') or e.get('sku', '')}`"
        if kind == "variant":
            opts = " / ".join(str(v) for v in e.get("options", {}).values())
            if opts:
                desc += "\n옵션: " + opts
            desc += f"\n조회 로케일: {e.get('locale', 'unknown')}"
            qty = e.get("quantity")
            if qty is None:
                desc += "\n재고 수량: 미공개"
            elif e.get("quantity_kind") == "capped":
                desc += f"\n재고 수량: {qty}개 이상 (응답 상한)"
            else:
                desc += f"\n재고 수량: {qty}개 (검증된 공개 필드)"
        desc += f"\n상태 변화: {old} → **{status}**"
        if e.get("evidence"):
            desc += "\n근거: " + e["evidence"]
    elif kind == "health":
        desc = f"• **{title}**\n{e['message']}"
    else:
        desc = f"• **{e['selector']}** 영역 변경\n변경 전: {e['before']}\n변경 후: {e['after']}"
    if e.get("url"):
        desc += "\n" + e["url"]
    if e.get("observed_at"):
        stamp = datetime.fromisoformat(e["observed_at"]).astimezone(ZoneInfo("Asia/Seoul"))
        desc += "\n확인 시각(KST): " + stamp.strftime("%Y-%m-%d %H:%M:%S")
    return desc


def send_discord(m: dict, events: list[dict], *, on_sent=None) -> None:
    """배치가 성공할 때마다 해당 이벤트만 확인 처리한다. 모든 내용은 분할 전송한다."""
    if not events:
        return
    url = _discord_url()
    mention_id = os.getenv("DISCORD_USER_ID", "").strip()
    mentions = {"parse": []}
    mention = ""
    if mention_id:
        if not re.fullmatch(r"\d{15,22}", mention_id):
            raise ValueError("DISCORD_USER_ID는 숫자로 된 Discord 사용자 ID만 지원합니다")
        mentions = {"parse": [], "users": [mention_id]}
        mention = f"<@{mention_id}> "
    limit = min(15, max(1, int(m.get("notify_limit", 8))))
    batches, fragments, completed, length = [], [], [], 0
    for event in events:
        parts = _discord_parts(_event_description(event))
        for index, part in enumerate(parts):
            addition = _discord_len(part) + (2 if fragments else 0)
            if fragments and (length + addition > 3900 or len(completed) >= limit):
                batches.append((fragments, completed))
                fragments, completed, length = [], [], 0
            length += _discord_len(part) + (2 if fragments else 0)
            fragments.append(part)
            if index == len(parts) - 1:
                completed.append(event)
    if fragments:
        batches.append((fragments, completed))
    for fragments, completed in batches:
        name = str(m.get("name", m["id"]))[:100]
        embed = {"title": name + " 변경 알림", "description": "\n\n".join(fragments),
                 "url": m["url"], "color": 0xC0C0C0}
        thumb = next((e.get("image", "") for e in completed
                      if str(e.get("image", "")).startswith("https://")), "")
        if thumb:
            embed["thumbnail"] = {"url": thumb}
        payload = {"content": mention + "🔔 " + name + ": 감시 알림",
                   "embeds": [embed], "allowed_mentions": mentions}
        traffic = _TRAFFIC.get()
        for retry in range(4):
            timeout = traffic.timeout(20) if traffic else 20
            response = requests.post(url, json=payload, timeout=timeout, allow_redirects=False)
            if response.status_code in (200, 204):
                if on_sent and completed:
                    on_sent(completed)
                break
            if response.status_code == 429 and retry < 3:
                try:
                    wait = min(60, max(1.0, float(response.json().get("retry_after", 2))))
                except (ValueError, AttributeError, TypeError):
                    wait = 2
                if traffic and traffic.clock() + wait >= traffic.deadline:
                    raise ScanDeadline()
                time.sleep(wait)
                continue
            if response.status_code >= 500 and retry < 3:
                if traffic and traffic.clock() + retry + 1 >= traffic.deadline:
                    raise ScanDeadline()
                time.sleep(retry + 1)
                continue
            raise RuntimeError(f"Discord 전송 실패: HTTP {response.status_code}")


def _enqueue(state: dict, m: dict, events: list[dict]) -> None:
    queue = state.setdefault("pending_notifications", [])
    if len(queue) + len(events) > MAX_SEEN:
        raise ValueError("미전송 알림 한도 초과. 웹훅/상태 파일을 확인하세요")
    info = {k: m[k] for k in ("id", "name", "url", "notify_limit") if k in m}
    for event in events:
        state["notification_sequence"] = state.get("notification_sequence", 0) + 1
        queue.append({"id": state["notification_sequence"], "monitor": info,
                      "event": {**event, "_notification_id": state["notification_sequence"]}})


def _flush_notifications(state: dict, state_path: Path, *, checkpoint=None) -> None:
    if state.get("pending_notifications"):
        save_state(state_path, state)
        if checkpoint:
            # 다음 runner가 복구할 큐를 먼저 저장한다. 저장 실패 시 외부 전송을 시작하지 않는다.
            checkpoint()
    while state.get("pending_notifications"):
        entries = state["pending_notifications"]
        monitor = entries[0]["monitor"]
        group = []
        for entry in entries:
            if entry["monitor"] != monitor:
                break
            group.append(entry["event"])

        def acknowledged(events):
            ids = {event["_notification_id"] for event in events}
            remaining = [entry for entry in state["pending_notifications"] if entry["id"] not in ids]
            save_state(state_path, dict(state, pending_notifications=remaining))
            state["pending_notifications"] = remaining
            if checkpoint:
                checkpoint()

        send_discord(monitor, group, on_sent=acknowledged)


def _record_health(state: dict, key: str, name: str, url: str, *, error: str = "", duration: float = 0) -> list[dict]:
    previous = copy.deepcopy(_LIVE_HEALTH.get(key) or state.get("health", {}).get(key, {}))
    now = _when()
    health = dict(previous, last_checked_at=now, duration_seconds=round(duration, 2))
    if previous.get("last_checked_at"):
        health["actual_interval_seconds"] = round(_age_seconds(previous["last_checked_at"]), 2)
    events = []
    if error:
        health["consecutive_failures"] = previous.get("consecutive_failures", 0) + 1
        health["last_error"] = error[:180]
        if health["consecutive_failures"] >= 3 and not previous.get("alerted", False):
            health["alerted"] = True
            events.append({"kind": "health", "title": name + " 감시 오류",
                           "message": f"연속 {health['consecutive_failures']}회 확인 실패. 재고 없음으로 처리하지 않았습니다.\n{error[:180]}",
                           "url": url, "observed_at": now})
    else:
        health.update(last_success_at=now, consecutive_failures=0, last_error="", alerted=False, status="ok")
        health.pop("expected_missing_status", None)
        if previous.get("alerted", False):
            events.append({"kind": "health", "title": name + " 감시 복구",
                           "message": "정상 응답 확인을 재개했습니다.", "url": url, "observed_at": now})
    _LIVE_HEALTH[key] = health
    saved = state.setdefault("health", {}).get(key, {})
    if (error or previous.get("consecutive_failures", 0) or saved.get("status") != health.get("status")
            or _age_seconds(saved.get("last_checked_at")) >= HEALTH_CHECKPOINT_SECONDS):
        state["health"][key] = health
    return events


def _error_text(exc: Exception) -> str:
    msg = str(exc)
    webhook = os.getenv("DISCORD_WEBHOOK_URL", "").strip()
    if webhook:
        msg = msg.replace(webhook, "<redacted-webhook>")
        path = urlsplit(webhook).path
        if path:
            msg = msg.replace(path, "<redacted-webhook-path>")
    return re.sub(r"(/api(?:/v\d+)?/webhooks/\d+/)[A-Za-z0-9_-]+", r"\1<redacted>", msg)[:180]


# 사이즈 감시는 기존 config에도 기본 활성화된다. 실행 주기/Actions 설정은 바꾸지 않는다.
# 목록·탐색 후 남은 요청 예산으로 상세 상품을 순환 확인한다.
# 선택 설정(각 monitor): track_variants=false, notify_on_first_variant_check=true,
# inventory_quantity_path="inventory.ats", inventory_quantity_verified=true,
# inventory_quantity_cap=100. 수량 필드의 의미/상한이 검증된 경우에만 설정한다.


def _variation_url(base: str, raw: str) -> str:
    url = absolute_url(base, raw)
    if not url:
        return ""
    parts = urlsplit(url)
    if (parts.scheme, parts.netloc) != (urlsplit(base).scheme, urlsplit(base).netloc):
        return ""
    if not parts.path.endswith("/Product-Variation"):
        return ""
    pairs = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True) if k]
    params = dict(pairs)
    if not re.fullmatch(r"[A-Za-z0-9_-]{6,60}", params.get("pid", "")):
        return ""
    # 선택된 옵션을 다시 누르는 URL은 선택 해제 요청이다. 수량 탐색도 하지 않는다.
    if any(k.startswith("dwvar_") and not v for k, v in pairs):
        return ""
    if params.get("quantity", "1") != "1":
        return ""
    return urlunsplit((parts.scheme, parts.netloc, parts.path, urlencode(sorted(pairs)), ""))


def _variation_seeds(html: str, base: str, allowed_pids: set[str] | None = None) -> list[str]:
    soup = BeautifulSoup(html, "html.parser")
    urls = []
    # 기본 옵션 URL을 먼저 조회한다. 실제 HTML에 존재하는 URL만 사용한다.
    for node in [*soup.select("[data-defaultvariant-url]"), *soup.find_all(True)]:
        for value in node.attrs.values():
            if isinstance(value, str) and "Product-Variation?" in value:
                url = _variation_url(base, value)
                pid = dict(parse_qsl(urlsplit(url).query)).get("pid", "")
                if url and url not in urls and (allowed_pids is None or pid in allowed_pids):
                    urls.append(url)
    return urls


def _quantity(product: dict, options: dict) -> tuple[int | None, str, str]:
    path = options.get("inventory_quantity_path", "")
    if not path or options.get("inventory_quantity_verified") is not True:
        return None, "undisclosed", ""
    if not isinstance(path, str) or any(part.lower() in {
            "maxorderquantity", "minorderquantity", "selectedquantity", "quantities"
    } for part in path.split(".")):
        return None, "undisclosed", ""
    value = product
    for part in path.split("."):
        value = value.get(part) if isinstance(value, dict) else None
    if isinstance(value, bool) or not isinstance(value, (int, float)) or value < 0:
        return None, "undisclosed", ""
    # NaN/무한대/소수/플랫폼 기본 센티널은 정확한 상품 수량으로 해석하지 않는다.
    if not value < 999999 or int(value) != value:
        return None, "undisclosed", ""
    cap = options.get("inventory_quantity_cap")
    kind = "capped" if isinstance(cap, (int, float)) and cap > 0 and value >= cap else "exact"
    return int(cap if kind == "capped" else value), kind, path


def _parse_variant(data: dict, lookup_url: str, target: dict) -> tuple[dict | None, list[str]]:
    if not isinstance(data, dict) or not isinstance(data.get("product"), dict):
        raise ValueError("옵션 응답에 product 객체가 없습니다")
    product = data["product"]
    pid = str(product.get("id", ""))
    family = str(product.get("masterProductId", ""))
    allowed = {target["pid"], target.get("master_pid", "")}
    if not ({pid, family} & (allowed - {""})):
        raise ValueError("옵션 응답이 요청한 상품과 일치하지 않습니다")
    attrs = product.get("variationAttributes", [])
    if not isinstance(attrs, list):
        raise ValueError("옵션 목록 형식이 올바르지 않습니다")
    selected = {}
    links = []
    for attr in attrs:
        name = str(attr.get("id") or attr.get("attributeId", ""))
        values = attr.get("values", [])
        for value in values:
            if value.get("selected") is True:
                selected[name] = {"id": str(value.get("id") or value.get("value", "")),
                                  "label": str(value.get("displayValue") or value.get("value", ""))}
            url = _variation_url(target["url"], str(value.get("url", "")))
            if url and url not in links:
                links.append(url)
    if attrs and (len(selected) != len(attrs) or product.get("productType") != "variant"):
        return None, links
    for attr, selection in selected.items():
        requested = [v for k, v in parse_qsl(urlsplit(lookup_url).query)
                     if k.startswith("dwvar_") and k.endswith("_" + attr)]
        if requested and any(v != selection["id"] for v in requested):
            raise ValueError("선택한 옵션과 응답 옵션이 다릅니다")
    messages = " ".join(str(x) for x in product.get("availability", {}).get("messages", []))
    if product.get("isProductRestricted") is True:
        status = "restricted"
    elif product.get("online") is False:
        status = "unavailable"
    elif COMING_SOON.search(messages):
        status = "coming_soon"
    elif product.get("readyToOrder") is not True:
        status = "selection_required"
    elif product.get("available") is True:
        status = "available"
    elif product.get("available") is False:
        status = "sold_out"
    else:
        status = "unknown"
    qty, kind, source = _quantity(product, target.get("options", {}))
    url = absolute_url(target["url"], str(product.get("selectedProductUrl", ""))) or target["url"]
    if not product_pid(target["url"], url)[0]:
        url = target["url"]
    locale = str(data.get("locale", "unknown"))
    return {"pid": pid, "master_pid": family or target["pid"],
            "title": str(product.get("productName") or target["title"])[:260],
            "color": selected.get("color", {}).get("label", ""),
            "size": selected.get("size", {}).get("label", ""),
            "options": {k: v["label"] for k, v in selected.items()},
            "status": status, "quantity": qty, "quantity_kind": kind,
            "quantity_source": source, "locale": locale,
            "url": url, "lookup_url": lookup_url}, links


class _BudgetExhausted(Exception):
    pass


def _detail_get(session, url: str, budget: list[int], *, referer: str = ""):
    host = urlsplit(url).hostname or ""
    if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
        raise _BudgetExhausted("사이트 접근 차단 후 대기 중")
    if budget[0] <= 0:
        raise _BudgetExhausted("이번 순회의 상세 조회 요청 한도")
    headers = {"User-Agent": "PageWatch/1.0 (read-only personal monitor)",
               "Accept-Language": "en-US,en;q=0.9"}
    if referer:
        headers.update({"Referer": referer, "Accept": "application/json"})
    response = _site_get(session.get, url, headers=headers, budget=budget)
    response.raise_for_status()
    if (urlsplit(response.url).hostname or "") != host:
        raise ValueError("상품 조회가 다른 도메인으로 이동했습니다")
    return response


def _register_products(state: dict, m: dict, previous: dict | None, events: list[dict]) -> None:
    if not m.get("track_variants", True):
        return
    targets = state.setdefault("tracked_products", {})
    announce_urls = {e.get("url") for e in events if e["kind"] in
                     ("new_product", "reappeared", "item", "item_reappeared")}
    for product in m.get("_products", []):
        pid, url = product_pid(m["url"], product["url"])
        if not pid:
            continue
        key = (urlsplit(url).hostname or "") + ":" + pid
        if key not in targets:
            if len(targets) >= MAX_SEEN:
                raise ValueError("상세 감시 상품 한도 초과: 상태 파일 확인 필요")
            targets[key] = {"pid": pid, "url": url, "title": product["title"],
                            "variants": {}, "sources": {}, "baseline_complete": False,
                            "notify_initial": bool(m.get("notify_on_first_variant_check", False)
                                                   or url in announce_urls),
                            "last_checked_at": "", "options": {}}
        target = targets[key]
        target["sources"][m["id"]] = True
        target["title"] = product["title"]
        target["url"] = url
        if url in announce_urls:
            target["priority"] = True
        for option in ("inventory_quantity_path", "inventory_quantity_verified", "inventory_quantity_cap",
                       "notify_on_sold_out", "notify_on_unavailable", "notify_on_restock"):
            if option in m:
                target["options"][option] = m[option]
    if m.get("mode") == "catalog" and m.get("_catalog_complete", True):
        current = state["monitors"].get(m["id"], {}).get("seen", {})
        absent = {x["url"] for x in current.values() if x.get("present") is False}
        for target in targets.values():
            if target["url"] in absent and m["id"] in target["sources"]:
                target["sources"][m["id"]] = False


def _accept_observation(state: dict, monitor: dict, current: dict | None,
                        events: list[dict], record_events) -> None:
    """등록 검증과 큐 수락이 끝난 관측만 적용한다. 실패 시 신규 판단의 기준을 유지한다."""
    staged = dict(state, monitors=dict(state["monitors"]),
                  tracked_products=copy.deepcopy(state.get("tracked_products", {})))
    previous = state["monitors"].get(monitor["id"])
    if current is not None:
        staged["monitors"][monitor["id"]] = current
    _register_products(staged, monitor, previous, events)
    record_events(monitor, events)
    state["tracked_products"] = staged["tracked_products"]
    if current is not None:
        state["monitors"][monitor["id"]] = current


def _merge_variant(target: dict, row: dict) -> list[dict]:
    key = row["pid"] + ":" + row["locale"]
    previous = target.setdefault("variants", {}).get(key)
    old_status = (previous or {}).get("last_known_status", (previous or {}).get("status"))
    known = row["status"] not in ("unknown", "selection_required", "listed")
    row["last_known_status"] = row["status"] if known else old_status
    row["last_seen_at"] = _seen_stamp(previous or {}, _when(), previous is None or row["status"] != (previous or {}).get("status"))
    target["variants"][key] = row
    options = target.get("options", {})
    initial_alert = target.get("notify_initial", False) or target.get("baseline_complete", False)
    notify = row["status"] == "available" and old_status != "available" and (previous is not None or initial_alert)
    if notify and not options.get("notify_on_restock", True):
        notify = False
    if previous is not None and known and old_status != row["status"]:
        notify |= row["status"] == "sold_out" and bool(options.get("notify_on_sold_out", False))
        notify |= row["status"] in ("restricted", "unavailable") and bool(options.get("notify_on_unavailable", False))
    if not notify:
        return []
    return [{"kind": "variant", **row, "previous_status": old_status, "observed_at": _when()}]


def check_product_variants(session, target: dict, budget: list[int]) -> tuple[dict, list[dict]]:
    """실제 페이지/응답의 GET 링크만 읽는다. 장바구니/주문/추정 수량 요청은 하지 않는다."""
    target = copy.deepcopy(target)
    response = _detail_get(session, target["url"], budget)
    pid, _ = product_pid(target["url"], response.url)
    if not pid or pid not in {target["pid"], target.get("master_pid")}:
        raise ValueError("상품 페이지가 메인/다른 상품으로 이동했습니다")
    html = response.text
    soup = BeautifulSoup(html, "html.parser")
    if not soup.find("h1") or any(p in _visible_text(soup).lower()[:3000] for p in CAPTCHA_PHRASES):
        raise ValueError("상품 페이지가 아니거나 접근 확인이 필요합니다")
    seeds = _variation_seeds(html, target["url"], {target["pid"], target.get("master_pid", "")})
    if not seeds and not target.get("scan_queue") and not any(
            v.get("lookup_url") for v in target.get("variants", {}).values()):
        result = detect_availability(html, {"url": target["url"], "expected_pid": target["pid"]})
        # 옵션을 선택하지 않은 PDP의 CTA를 사이즈별 재고로 확대 해석하지 않는다.
        if soup.select("[data-attr], [class*=size-selector], [class*=swatch]"):
            raise ValueError("옵션이 있지만 공개 옵션 조회 URL을 찾지 못했습니다")
        row = {"pid": target["pid"], "title": result["title"], "color": "", "size": "",
               "options": {}, "status": result["status"], "quantity": None,
               "quantity_kind": "undisclosed", "quantity_source": "", "locale": "page",
               "url": target["url"], "lookup_url": ""}
        events = _merge_variant(target, row)
        target.update(baseline_complete=True, notify_initial=False, priority=False, last_checked_at=_when())
        return target, events
    seen = set(target.get("scan_seen", []))
    queue = deque()
    queued = set()

    def add_url(raw):
        url = _variation_url(target["url"], raw)
        if url and url not in seen and url not in queued:
            # 매우 큰/비정상 옵션 그래프가 상태 파일을 무한히 키우지 않게 중단한다.
            if len(seen) + len(queued) >= 500:
                raise ValueError("상품 옵션 URL 한도 초과")
            queue.append(url)
            queued.add(url)

    for raw in [*target.get("scan_queue", []),
                *(v.get("lookup_url", "") for v in target["variants"].values()), *seeds]:
        add_url(raw)
    if not queue:
        raise ValueError("검증 가능한 상품 옵션 조회 URL이 없습니다")
    events = []
    requests_used = 0
    observed = 0
    while queue and budget[0] > 0 and requests_used < 12:
        url = queue[0]
        try:
            response = _detail_get(session, url, budget, referer=target["url"])
        except _BudgetExhausted:
            break
        requests_used += 1
        # JSON이 아닌 로그인/차단 응답 또는 다른 상품 응답은 기존 정상 상태를 보존한다.
        row, links = _parse_variant(response.json(), url, target)
        queue.popleft()
        queued.discard(url)
        seen.add(url)
        if row:
            observed += 1
            target["master_pid"] = row.get("master_pid", target["pid"])
            events += _merge_variant(target, row)
        for link in links:
            add_url(link)
    if not observed and not queue:
        raise ValueError("완전히 선택된 상품 옵션 응답을 확인하지 못했습니다")
    target["scan_queue"] = list(queue)
    target["scan_seen"] = sorted(seen) if queue else []
    if not queue:
        target["baseline_complete"] = True
        target["notify_initial"] = False
    target["last_checked_at"] = _when()
    target["priority"] = False
    return target, events


def run(config_path: Path, state_path: Path, *, dry_run: bool = False, checkpoint=None, traffic=None) -> int:
    traffic = traffic or SiteTraffic()
    traffic.count = 0
    token = _TRAFFIC.set(traffic)
    try:
        return _run_checks(config_path, state_path, dry_run=dry_run, checkpoint=checkpoint, traffic=traffic)
    finally:
        _TRAFFIC.reset(token)


def _run_checks(config_path, state_path, *, dry_run, checkpoint, traffic):
    config = json.loads(config_path.read_text(encoding="utf-8"))
    monitors = config.get("monitors", [])
    if not isinstance(monitors, list):
        raise ValueError("config의 monitors는 배열이어야 합니다")
    active = [dict(m) for m in monitors if m.get("enabled", False)]
    if not active:
        print("[설정 필요] enabled=true인 감시 대상이 없습니다.")
        return 2
    ids = [m.get("id") for m in active]
    if len(set(ids)) != len(ids):
        raise ValueError("같은 monitor id를 두 번 사용할 수 없습니다")
    for m in active:
        validate_monitor(m)
    state = load_state(state_path)
    traffic.recovery = state.get("site_recovery", {})
    if traffic.recovery.get("until", 0) <= time.time():
        traffic.recovery = {}
        state.pop("site_recovery", None)
    backoffs = state.setdefault("site_backoffs", {})
    for host, until in list(backoffs.items()):
        if until <= time.time():
            del backoffs[host]
        elif host not in _SITE_BLOCKED_UNTIL:
            _SITE_BLOCKED_UNTIL[host] = time.monotonic() + until - time.time()
    discovery_audits = [DiscoveryAudit(state, m, active) for m in list(active) if m.get("mode") == "discovery"]
    for audit in discovery_audits:
        audit.restore()
    errors = 0
    counts = {"events": 0, "pages": 0, "paused": 0, "details": 0, "inactive": 0, "deferred": 0}

    def persist():
        if not dry_run:
            save_state(state_path, state)

    def record_events(m, events):
        _enqueue(state, m, events)
        counts["events"] += len(events)

    def failed(m, key, exc, started):
        nonlocal errors
        errors += 1
        msg = _error_text(exc)
        if isinstance(exc, SiteAccessDenied):
            host, backoff = exc.host, exc.delay
            _SITE_BLOCKED_UNTIL[host] = max(_SITE_BLOCKED_UNTIL.get(host, 0), time.monotonic() + backoff)
            backoffs[host] = max(backoffs.get(host, 0), time.time() + backoff)
            traffic.recovery = {"factor": min(8, 2 * traffic.recovery.get("factor", 1)),
                                "until": backoffs[host] + OPTIONAL_RECHECK}
            state["site_recovery"] = traffic.recovery
            persist()
            print(f"[BLOCKED] {key}: HTTP {exc.status}, 같은 도메인 {backoff}초 대기", file=sys.stderr)
        else:
            print(f"[ERROR] {key}: {type(exc).__name__}: {msg}", file=sys.stderr)
        record_events(m, _record_health(state, key, m.get("name", key), m["url"],
                                       error=msg, duration=time.monotonic() - started))
        persist()

    if not dry_run and state.get("pending_notifications"):
        try:
            _flush_notifications(state, state_path, checkpoint=checkpoint)
        except ScanDeadline:
            counts["deferred"] += 1
        except Exception as exc:
            errors += 1
            print(f"[NOTIFY] 이전 알림 재전송 실패: {_error_text(exc)}", file=sys.stderr)

    def check_all(browser=None):
        trials = state.setdefault("optional_probes", {})
        visible = {v["url"] for audit in discovery_audits
                   for v in state["monitors"].get(audit.monitor["id"], {}).get("snapshot", {}).values()}
        # 홈페이지를 먼저 읽으면 새 메뉴가 대기 중인 후보라도 이 순회에서 확인할 수 있다.
        ordered = sorted(active, key=lambda m: (m.get("mode") != "discovery",
                         bool(m.get("optional_catalog")), trials.get(m["id"], "")))
        speculative = 0
        for m in ordered:
            host = urlsplit(m["url"]).hostname or ""
            if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
                counts["paused"] += 1
                continue
            previous = state["monitors"].get(m["id"])
            prior_trial = trials.get(m["id"])
            if m.get("optional_catalog") and not (previous or {}).get("seen") and m["url"] not in visible:
                health = state.get("health", {}).get(m["id"], {})
                unlisted = (health.get("status") == "inactive" or (previous or {}).get("last_count") == 0)
                if speculative >= 2 or (unlisted and not health.get("consecutive_failures")
                                        and _age_seconds(prior_trial) < OPTIONAL_RECHECK):
                    counts["deferred"] += 1
                    continue
                speculative += 1
                trials[m["id"]] = _when()
            started = time.monotonic()
            try:
                html = fetch_html(m, browser)
                # 파싱 실패한 페이지의 자식 분류도 관측한다. 중간 분류 페이지를 버리지 않는다.
                for audit in discovery_audits:
                    if (urlsplit(m["url"]).hostname or "").removeprefix("www.") == (urlsplit(audit.base).hostname or "").removeprefix("www."):
                        audit.observe(html, m.get("_final_url", m["url"]))
                if (m.get("optional_catalog") and not urlsplit(m.get("_final_url", m["url"])).path.strip("/")
                        and (previous or {}).get("seen")):
                    raise ValueError("게시된 카테고리가 홈페이지로 이동했습니다. 기존 상품을 유지합니다")
                current, events = compare(m, previous, html)
                if m.get("mode") == "discovery":
                    visible.update(item["url"] for item in current.get("snapshot", {}).values())
                # 이벤트를 큐에 넣은 뒤 상태를 저장한다. 웹훅 오류로 이벤트가 사라지지 않는다.
                _accept_observation(state, m, current, events, record_events)
                record_events(m, _record_health(state, m["id"], m.get("name", m["id"]), m["url"],
                                               duration=time.monotonic() - started))
                persist()
                counts["pages"] += 1
                print(f"[OK] {m['id']}: {current.get('status', str(current.get('last_count', len(current.get('regions', [])))))}"
                      f" / 새 알림 {len(events)}건 / {time.monotonic() - started:.1f}초"
                      + (" (dry run, 미전송/미저장)" if dry_run else ""))
            except ScanDeadline:
                if prior_trial is None:
                    trials.pop(m["id"], None)
                else:
                    trials[m["id"]] = prior_trial
                counts["deferred"] += 1
                return
            except CatalogNotFound as exc:
                previous = state["monitors"].get(m["id"], {})
                if not m.get("optional_catalog") or previous.get("seen"):
                    # 이전에 상품이 있던 실제 카테고리의 404/410은 계속 오류로 알린다.
                    failed(m, m["id"], exc, started)
                    continue
                counts["inactive"] += 1
                old = state.setdefault("health", {}).get(m["id"], {})
                health = dict(old, last_checked_at=_when(), status="inactive", consecutive_failures=0,
                              alerted=False, last_error=str(exc), expected_missing_status=exc.status)
                _LIVE_HEALTH[m["id"]] = health
                if old.get("status") != "inactive" or _age_seconds(old.get("last_checked_at")) >= HEALTH_CHECKPOINT_SECONDS:
                    state["health"][m["id"]] = health
                    print(f"[INACTIVE] {m['id']}: HTTP {exc.status}; 아직 게시되지 않은 선택적 후보, 계속 재확인")
                    persist()
            except Exception as exc:
                failed(m, m["id"], exc, started)

        for audit in discovery_audits:
            try:
                audit.scan(browser, record_events, lambda m, duration: record_events(
                    m, _record_health(state, m["id"], m["name"], m["url"], duration=duration)))
            except ScanDeadline:
                counts["deferred"] += 1
                return
            except Exception as exc:
                failed(audit.monitor, audit.monitor["id"] + "-extra-discovery", exc, time.monotonic())
            persist()

    with ExitStack() as stack:
        browser = None

        def get_browser():
            nonlocal browser
            if browser is not None:
                return browser
            from playwright.sync_api import sync_playwright
            playwright = stack.enter_context(sync_playwright())
            browser = playwright.chromium.launch(headless=True)
            stack.callback(browser.close)
            return browser

        check_all(get_browser if any(m.get("render") in ("browser", "auto") for m in active) else None)

    # 신상품과 기존 상품 중 가장 오래 기다린 항목을 교대로 처리한다.
    # 모든 옵션을 한 순회에서 읽지 못하면 scan_queue를 보존하여 이어서 진행한다.
    enabled_sources = {m["id"] for m in active if m.get("track_variants", True)}
    targets = state.get("tracked_products", {})
    candidates = [(key, target) for key, target in targets.items()
                  if any(present and source in enabled_sources
                         for source, present in target.get("sources", {}).items())]
    candidates.sort(key=lambda pair: (pair[1].get("last_attempt_at", ""), pair[0]))
    new_products = deque(pair for pair in candidates if pair[1].get("priority"))
    regular = deque(pair for pair in candidates if not pair[1].get("priority"))
    # 목록/탐색이 소비한 실제 요청을 빼고, 목록이 급증해도 상세 조회에 최소 4회를 배정한다.
    budget = [min(48, max(4, traffic.round_size - traffic.count))]
    with requests.Session() as session:
        while (new_products or regular) and budget[0] >= 2 and traffic.clock() < traffic.deadline:
            both = bool(new_products and regular)
            prefer_new = state.get("detail_next_new", True) if both else bool(new_products)
            key, target = (new_products if prefer_new else regular).popleft()
            host = urlsplit(target["url"]).hostname or ""
            if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
                counts["paused"] += 1
                continue
            m = {"id": "variant-" + hashlib.sha256(key.encode()).hexdigest()[:16],
                 "name": "Chrome Hearts 사이즈 " + target["title"], "url": target["url"]}
            started = time.monotonic()
            try:
                current, events = check_product_variants(session, target, budget)
                current["last_attempt_at"] = _when()
                record_events(m, events)
                targets[key] = current
                if both:
                    state["detail_next_new"] = not prefer_new
                record_events(m, _record_health(state, m["id"], m["name"], m["url"],
                                               duration=time.monotonic() - started))
                persist()
                counts["details"] += 1
                print(f"[VARIANT] {target['pid']}: 저장된 옵션 {len(current['variants'])}개, "
                      f"다음 순회로 넘긴 URL {len(current.get('scan_queue', []))}개 / 새 알림 {len(events)}건")
            except (ScanDeadline, _BudgetExhausted):
                counts["deferred"] += 1
                persist()
                break
            except Exception as exc:
                target.update(last_attempt_at=_when(), priority=False)
                if both:
                    state["detail_next_new"] = not prefer_new
                failed(m, m["id"], exc, started)
    if not dry_run:
        try:
            _flush_notifications(state, state_path, checkpoint=checkpoint)
        except ScanDeadline:
            counts["deferred"] += 1
        except Exception as exc:
            errors += 1
            print(f"[NOTIFY] 알림 전송 실패, 미전송 항목 보존: {_error_text(exc)}", file=sys.stderr)
    print(f"총 {counts['pages']}개 페이지 / {counts['details']}개 상세 확인, "
          f"{counts['events']}건 감지, 실패 {errors}개, 접근차단 대기 {counts['paused']}개, "
          f"미게시 후보 {counts['inactive']}개, 다음 확인으로 넘김 {counts['deferred']}개, "
          f"대기 알림 {len(state.get('pending_notifications', []))}건")
    return 1 if errors or counts["paused"] or not any(counts[k] for k in ("pages", "details", "inactive", "deferred")) else 0


def git_checkpoint(state_path: Path) -> bool:
    """Commit and push monitor state immediately after a change, across workflow runs.

    Designed for a GitHub Actions checkout with contents:write and
    persist-credentials:true. A failed push raises so next loop retries.
    """
    if not Path(".git").exists():
        raise RuntimeError("git state sync는 GitHub Actions checkout에서만 사용할 수 있습니다")
    try:
        repo_path = str(state_path.resolve().relative_to(Path.cwd().resolve()))
    except ValueError as exc:
        raise ValueError("state 파일은 저장소 내부에 있어야 합니다") from exc
    branch = os.environ.get("GITHUB_REF_NAME", "").strip()
    if not branch or not re.fullmatch(r"[A-Za-z0-9._/-]{1,180}", branch) or branch.startswith("-"):
        raise ValueError("GITHUB_REF_NAME에 유효한 브랜치 이름이 필요합니다")

    def git(*args: str) -> subprocess.CompletedProcess:
        return subprocess.run(["git", *args], text=True, capture_output=True, check=True,
                              timeout=45)

    # Commit only actual state changes, but also retry previously failed pushes.
    changed = git("status", "--porcelain", "--", repo_path).stdout.strip()
    if changed:
        git("add", "--", repo_path)
        staged = subprocess.run(["git", "diff", "--cached", "--quiet", "--", repo_path])
        if staged.returncode not in (0, 1):
            raise RuntimeError("git diff 실패")
        if staged.returncode == 1:
            git("-c", "user.name=github-actions[bot]",
                "-c", "user.email=41898282+github-actions[bot]@users.noreply.github.com",
                "commit", "-m", "chore: save monitor state [skip ci]", "--", repo_path)

    # git pull and push only when there are local commits to upload.
    ahead = git("rev-list", "--count", "HEAD", "--not", f"origin/{branch}").stdout.strip()
    if int(ahead or "0") == 0:
        return bool(changed)
    try:
        git("pull", "--rebase", "origin", branch)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, KeyboardInterrupt):
        # 충돌/중단된 rebase를 다음 순회에 넘기지 않는다. 로컬 커밋은 보존한다.
        try:
            subprocess.run(["git", "rebase", "--abort"], capture_output=True, timeout=10, check=False)
        except subprocess.SubprocessError:
            print("[STATE] rebase 정리 실패: 저장소 상태 확인이 필요합니다.", file=sys.stderr)
        raise
    git("push", "origin", f"HEAD:refs/heads/{branch}")
    print("[STATE] 감시 상태를 GitHub 저장소에 저장했습니다.", flush=True)
    return True


def run_loop(
    config_path: Path,
    state_path: Path,
    *,
    interval_seconds: int,
    duration_seconds: int,
    git_sync: bool = False,
    dry_run: bool = False,
    check=None,
    checkpoint=None,
    clock=None,
    sleep=None,
) -> int:
    """One long-running job; checks every ~interval_seconds until its deadline.

    Unlike the reference KCA in-memory baseline, this stores state on disk and
    optionally pushes changed state, retaining alerts across job replacements.
    Test seams permit simulated time and requests without hitting external sites.
    """
    if interval_seconds < 1 or duration_seconds < 1:
        raise ValueError("감시 주기/실행 시간은 양수여야 합니다")
    if git_sync and dry_run:
        raise ValueError("--dry-run 및 --git-sync는 함께 사용할 수 없습니다")
    clock = clock or time.monotonic
    sleep = sleep or time.sleep
    checkpoint = checkpoint or (lambda: git_checkpoint(state_path))
    started = clock()
    deadline = started + duration_seconds
    if os.getenv("MONITOR_STOP_EPOCH"):
        deadline = min(deadline, started + max(0, int(os.environ["MONITOR_STOP_EPOCH"]) - time.time()))
    session = requests.Session()
    traffic = SiteTraffic(interval_seconds, clock=clock, sleep=sleep, get=session.get)
    traffic.deadline = deadline
    check = check or (lambda: run(config_path, state_path, dry_run=dry_run, traffic=traffic,
                                  checkpoint=checkpoint if git_sync else None))
    iteration = failures = successes = 0
    sync_failed = cancelled = False

    def sync_state():
        nonlocal sync_failed
        if not git_sync:
            return
        try:
            checkpoint()
            sync_failed = False
        except Exception as exc:
            sync_failed = True
            print(f"[STATE] 저장소 동기화 실패 ({type(exc).__name__}). 로컬 상태를 보존하고 재시도합니다.",
                  file=sys.stderr, flush=True)

    def terminate(_signum, _frame):
        raise KeyboardInterrupt()

    previous_term = None
    try:
        previous_term = signal.signal(signal.SIGTERM, terminate)
    except ValueError:
        # 라이브러리로 다른 스레드에서 호출된 경우 신호 소유권은 호출자에게 있다.
        pass
    print(f"[LOOP] 감시 시작: 기본 {interval_seconds}초, 이번 실행 예산 {deadline-started:.0f}초, "
          f"Git 동기화={'사용' if git_sync else '미사용'}", flush=True)
    try:
        while clock() < deadline:
            iteration += 1
            tick_start = clock()
            try:
                status = check()
                if status == 0:
                    successes += 1
                else:
                    failures += 1
                    print(f"[LOOP] #{iteration} 일부 감시 오류(코드 {status}) — 다음 주기 재시도", flush=True)
            except Exception as exc:
                failures += 1
                print(f"[LOOP] #{iteration} 감시 오류: {type(exc).__name__}: {_error_text(exc)}",
                      file=sys.stderr, flush=True)
            sync_state()
            remaining = deadline - clock()
            if remaining <= 0:
                break
            interval = traffic.cycle_interval
            print(f"[PACE] 사이트 요청 {traffic.count}회, 요청 시작 간격 {traffic.gap:.2f}초, "
                  f"순회 목표 {interval}초, 이번 순회 {clock()-tick_start:.1f}초", flush=True)
            next_tick = tick_start + interval
            pause = min(remaining, max(0.0, next_tick - clock()))
            if pause > 0:
                sleep(pause)
    except KeyboardInterrupt:
        cancelled = True
        print("[LOOP] 종료 요청: 보존된 상태의 최종 동기화를 시도합니다.", flush=True)
    finally:
        try:
            sync_state()
        finally:
            session.close()
            if previous_term is not None:
                signal.signal(signal.SIGTERM, previous_term)
    print(f"[LOOP] 종료: 확인 {iteration}회, 성공 {successes}회, 오류 {failures}회, "
          f"동기화 실패={sync_failed}, 취소={cancelled}", flush=True)
    if cancelled:
        return 130
    return 0 if successes and not sync_failed else 1




def probe_site(config_path: Path, state_path: Path | None = None) -> int:
    with requests.Session() as session:
        token = _TRAFFIC.set(SiteTraffic(get=session.get))
        try:
            backoffs = load_state(state_path).get("site_backoffs", {}) if state_path else {}
            return _probe_targets(config_path, backoffs)
        finally:
            _TRAFFIC.reset(token)


def _probe_targets(config_path, backoffs):
    """GitHub 실행 환경에서 chromehearts.com에 접근 가능한지 진단(알림/상태 변경 없음).

    403/429는 '재고 없음'이 아니라 사이트가 이 실행 환경의 접근을 거부한 것이다.
    HTTP 응답 상태, 상품 링크 수, 품절 표기 수만 출력하며 응답 본문/쿠키는 출력하지 않는다.
    """
    config = json.loads(config_path.read_text(encoding="utf-8"))
    monitors = config.get("monitors", [])
    if not isinstance(monitors, list):
        raise ValueError("config의 monitors는 배열이어야 합니다")
    targets = []
    for m in monitors:
        if isinstance(m, dict) and m.get("url") and m["url"] not in [t["url"] for t in targets]:
            targets.append(m)
    if not targets:
        print("[PROBE] config/monitors.json에 url이 없습니다.")
        return 2
    reachable = 0
    for m in targets:
        try:
            url = safe_url(str(m["url"]))
            if backoffs.get(urlsplit(url).hostname, 0) > time.time():
                print(f"[PROBE] {m['id']}: 저장된 사이트 대기 시각까지 조회 보류")
                break
            response = _site_get(requests.get, url, timeout=20,
                                    headers={"User-Agent": "PageWatch/1.0 (read-only personal monitor)",
                                             "Accept-Language": "en-US,en;q=0.9"})
            status = response.status_code
            ctype = response.headers.get("content-type", "unknown")[:80]
            line = f"[PROBE] {m.get('id', '?')}: HTTP {status} | {ctype}"
            if status == 200:
                reachable += 1
                sample = dict(m, mode="catalog", url=url)
                products = extract_catalog(response.text, sample)
                sold = sum(1 for p in products if p["status"] == "sold_out")
                line += f" | 상품 링크 {len(products)}개 (품절 표기 {sold}개)"
                if m.get("mode") == "catalog" and not products:
                    line += " — 정적 HTML에 상품이 없으면 render=browser 사용"
            print(line, flush=True)
        except SiteAccessDenied as exc:
            print(f"[PROBE] {exc}; 진단 종료", flush=True)
            break
        except (requests.RequestException, ValueError) as exc:
            # 응답 본문/쿠키/인증정보는 출력하지 않는다.
            print(f"[PROBE] {m.get('id', '?')}: 요청 실패 ({type(exc).__name__})", flush=True)
    print(f"[PROBE] 완료: {len(targets)}개 URL 중 {reachable}개 접근 가능.")
    # 진단 작업은 사이트가 전부 거부해도 정상 종료한다.
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="크롬하츠 전용 쪽감시자 — 신상품/재입고/구매 가능 Discord 알림")
    parser.add_argument("--config", default="config/monitors.json")
    parser.add_argument("--state", default="state/monitor_state.json")
    parser.add_argument("--dry-run", action="store_true", help="전송/저장하지 않고 확인만 함")
    parser.add_argument("--test-webhook", action="store_true", help="Discord 웹훅 연결 점검")
    parser.add_argument("--probe-site", action="store_true", help="chromehearts.com 접근 가능 여부 진단(알림/상태변경 없음)")
    parser.add_argument("--loop", action="store_true", help="GitHub Actions 실행 중 반복 감시")
    parser.add_argument("--git-sync", action="store_true", help="상태 변경 즉시 GitHub에 커밋/푸시(Actions 전용)")
    parser.add_argument("--interval-seconds", type=int,
                        default=int(os.getenv("CHECK_INTERVAL_SECONDS", str(DEFAULT_INTERVAL))))
    parser.add_argument("--duration-seconds", type=int,
                        default=int(os.getenv("RUN_DURATION_SECONDS", str(DEFAULT_DURATION))))
    args = parser.parse_args()
    if args.probe_site:
        return probe_site(Path(args.config), Path(args.state))
    if args.test_webhook:
        _discord_url()
        m = {"id": "test", "name": "크롬하츠 쪽감시자 연결 테스트", "url": "https://example.com", "notify_limit": 1}
        send_discord(m, [{"kind": "region", "selector": "테스트", "before": "", "after": "알림 수신 성공"}])
        print("Discord 연결 테스트를 전송했습니다.")
        return 0
    if args.loop:
        return run_loop(Path(args.config), Path(args.state),
                        interval_seconds=args.interval_seconds,
                        duration_seconds=args.duration_seconds,
                        git_sync=args.git_sync, dry_run=args.dry_run)
    return run(Path(args.config), Path(args.state), dry_run=args.dry_run)


if __name__ == "__main__":
    sys.exit(main())
