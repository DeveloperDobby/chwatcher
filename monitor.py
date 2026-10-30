#!/usr/bin/env python3
"""크롬하츠(chromehearts.com) 전용 쪽감시자: 신상품 등록, 재입고/판매 시작,
개별 상품 구매 가능(Add to Bag) 전환을 Discord로 알림.

- catalog      : 카테고리 목록 페이지(예: /scents, /socks)를 감시. 신규 상품, 품절→구매가능
                 재입고, (옵션) 구매가능→품절 변경을 상품코드(PID) 기준으로 추적.
- availability : 개별 상품 상세 페이지의 Add to Bag / Sold Out / Coming Soon 상태 감시.
- 상세 자동 추적: 발견한 상품의 공개 Product-Variation 응답으로 색상/사이즈별 상태 확인.
                 주문 수량 제한을 재고량으로 사용하지 않으며 기본 수량 표시는 '미공개'.
- 알림 큐      : state 파일에 미전송 이벤트를 저장하고 전송 성공한 이벤트만 제거.
- items/region : 범용 모드(선택자 기반)로 그대로 유지.

로그인 쿠키를 요청하거나 외부 서버에 인증정보를 보내지 않습니다. 403/429/캡차는
우회하지 않고 대기합니다. 기본값은 첫 실행 알림 없음입니다.
"""
from __future__ import annotations

import argparse
from collections import deque
import copy
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import unicodedata
from urllib.parse import urljoin, urlsplit, urlunsplit, parse_qsl, urlencode
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
_LIVE_HEALTH: dict[str, dict] = {}

# 도메인에서 403/429를 돌려주면 동일 환경에서 매분 재시도하지 않는다.
# 프로세스 동안만 기억하며, 재실행 시 첫 요청부터 다시 확인한다.
_SITE_BLOCKED_UNTIL: dict[str, float] = {}


class SiteAccessDenied(RuntimeError):
    """쇼핑몰에서 요청을 거절한 경우(상태 403/429). Discord 오류와 구분."""

    def __init__(self, url: str, status: int):
        self.status = status
        self.host = urlsplit(url).hostname or "unknown"
        super().__init__(f"HTTP {status}: {self.host} 사이트가 자동 요청을 거부했습니다")


def _block_backoff_seconds() -> int:
    """403/429 뒤 도메인별 재시도 대기(기본 15분, 최소 1분, 최대 1시간)."""
    raw = os.getenv("SITE_BLOCK_BACKOFF_SECONDS", "900")
    try:
        return min(3600, max(60, int(raw)))
    except ValueError:
        return 900

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
    if m.get("render", "http") not in ("http", "browser"):
        raise ValueError(f"{m['id']}: render는 http 또는 browser")
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
            if button.count() == 0 or not button.is_visible():
                m["_catalog_complete"] = True
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


def fetch_html(m: dict, browser=None) -> str:
    url = m["url"]
    if m.get("render", "http") == "http":
        resp = requests.get(url, timeout=25, headers={"User-Agent": "PageWatch/1.0 (read-only personal monitor)"})
        if resp.status_code in (403, 429):
            raise SiteAccessDenied(url, resp.status_code)
        resp.raise_for_status()
        m["_final_url"] = safe_url(resp.url)
        html = resp.text
        soup = BeautifulSoup(html, "html.parser")
        m["_catalog_complete"] = not any(
            LOAD_MORE.search(_visible_text(el)) for el in soup.select("button, a, [role=button]"))
    else:
        if browser is None:
            raise RuntimeError("browser 감시에 Playwright Chromium이 필요합니다")
        context = browser.new_context(locale="en-US", viewport={"width": 1440, "height": 900})
        try:
            page = context.new_page()
            response = page.goto(url, wait_until="domcontentloaded", timeout=35000)
            if response is not None and response.status in (403, 429):
                raise SiteAccessDenied(url, response.status)
            if response is not None and response.status >= 400:
                raise RuntimeError(f"HTTP {response.status}")
            m["_final_url"] = safe_url(page.url)
            mode = m.get("mode", "items")
            if mode == "discovery":
                # 메뉴 토글만 연다. 실제 상품/장바구니 링크는 클릭하지 않는다.
                shop = page.locator("button, [role=button], a").filter(
                    has_text=re.compile(r"^\s*shop\s*$", re.I)).first
                if shop.count() and shop.is_visible():
                    href = shop.get_attribute("href") or ""
                    if not href or href.startswith(("#", "javascript:")):
                        shop.click(timeout=3000)
            inactive = m.get("optional_catalog") and urlsplit(page.url).path.rstrip("/") == ""
            direct_product = bool(PRODUCT_PATH.search(urlsplit(page.url).path))
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
        finally:
            context.close()
    plain = BeautifulSoup(html, "html.parser").get_text(" ", strip=True).lower()
    if any(phrase in plain[:3000] for phrase in CAPTCHA_PHRASES):
        raise RuntimeError("접근 차단/캡차 페이지입니다. 우회하지 않고 감시를 중단합니다")
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


DISCOVERY_EXCLUDE = {"account", "cart", "checkout", "contact", "contact-us", "customer-service",
                     "locations", "login", "magazine", "order-status", "privacy", "search",
                     "shop", "stores", "wishlist", "general", "terms"}

def extract_discovery(html: str, m: dict) -> list[dict]:
    soup = BeautifulSoup(html, "html.parser")
    for el in soup.select("script, style, footer, noscript, template"):
        el.decompose()
    found = {}
    base_host = (urlsplit(m["url"]).hostname or "").removeprefix("www.")
    for a in soup.select("a[href]"):
        url = absolute_url(m["url"], str(a.get("href", "")))
        if not url:
            continue
        parts = urlsplit(url)
        if (parts.hostname or "").removeprefix("www.") != base_host:
            continue
        path = parts.path.rstrip("/")
        is_product = bool(PRODUCT_PATH.search(path))
        is_category = bool(re.fullmatch(r"/[a-z0-9][a-z0-9-]{1,60}", path, re.I))
        if not is_product and (not is_category or path[1:].lower() in DISCOVERY_EXCLUDE):
            continue
        url = urlunsplit(("https", parts.netloc, path, "", ""))
        title = normalized(a.get_text(" ", strip=True)) or (a.img.get("alt", "") if a.img else "") or path
        key = hashlib.sha256(url.encode()).hexdigest()[:32]
        found[key] = {"key": key, "title": str(title)[:260], "url": url}
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
        for retry in range(4):
            response = requests.post(url, json=payload, timeout=20, allow_redirects=False)
            if response.status_code in (200, 204):
                if on_sent and completed:
                    on_sent(completed)
                break
            if response.status_code == 429 and retry < 3:
                try:
                    wait = min(60, max(1.0, float(response.json().get("retry_after", 2))))
                except (ValueError, AttributeError, TypeError):
                    wait = 2
                time.sleep(wait)
                continue
            if response.status_code >= 500 and retry < 3:
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


def _flush_notifications(state: dict, state_path: Path) -> None:
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
            state["pending_notifications"] = [entry for entry in state["pending_notifications"]
                                               if entry["id"] not in ids]
            save_state(state_path, state)

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
        health.update(last_success_at=now, consecutive_failures=0, last_error="", alerted=False)
        if previous.get("alerted", False):
            events.append({"kind": "health", "title": name + " 감시 복구",
                           "message": "정상 응답 확인을 재개했습니다.", "url": url, "observed_at": now})
    _LIVE_HEALTH[key] = health
    saved = state.setdefault("health", {}).get(key, {})
    if error or previous.get("consecutive_failures", 0) or _age_seconds(saved.get("last_checked_at")) >= HEALTH_CHECKPOINT_SECONDS:
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
# 한 순회에서 최대 8개 상품/48개 읽기 요청을 처리하고 나머지는 다음 순회로 넘긴다.
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
    budget[0] -= 1
    headers = {"User-Agent": "PageWatch/1.0 (read-only personal monitor)",
               "Accept-Language": "en-US,en;q=0.9"}
    if referer:
        headers.update({"Referer": referer, "Accept": "application/json"})
    response = session.get(url, headers=headers, timeout=25)
    if response.status_code in (403, 429):
        _SITE_BLOCKED_UNTIL[host] = time.monotonic() + _block_backoff_seconds()
        raise SiteAccessDenied(url, response.status_code)
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
    if not seeds and not any(v.get("lookup_url") for v in target.get("variants", {}).values()):
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
        response = _detail_get(session, url, budget, referer=target["url"])
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


def run(config_path: Path, state_path: Path, *, dry_run: bool = False) -> int:
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
    known_urls = {urlsplit(m["url"]).path.rstrip("/") for m in active}
    discovery = state["monitors"].get("ch-discovery", {})
    for entry in discovery.get("seen", {}).values():
        url = entry.get("url", "")
        path = urlsplit(url).path.rstrip("/")
        if not re.fullmatch(r"/[a-z0-9][a-z0-9-]{1,60}", path, re.I) or path in known_urls:
            continue
        if len(known_urls) >= 100:
            break
        dynamic = {"id": "discovered-" + hashlib.sha256(path.encode()).hexdigest()[:16],
                   "name": "자동 발견 " + path, "url": url, "enabled": True,
                   "mode": "catalog", "render": "http", "optional_catalog": True,
                   "notify_on_first_run": True, "notify_on_new": True, "notify_on_restock": True}
        validate_monitor(dynamic)
        active.append(dynamic)
        known_urls.add(path)
    errors = 0
    counts = {"events": 0, "pages": 0, "paused": 0, "details": 0}

    def persist():
        if not dry_run:
            save_state(state_path, state)

    def record_events(m, events):
        counts["events"] += len(events)
        _enqueue(state, m, events)

    def failed(m, key, exc, started):
        nonlocal errors
        errors += 1
        msg = _error_text(exc)
        if isinstance(exc, SiteAccessDenied):
            host = urlsplit(m["url"]).hostname or ""
            backoff = _block_backoff_seconds()
            _SITE_BLOCKED_UNTIL[host] = time.monotonic() + backoff
            print(f"[BLOCKED] {key}: HTTP {exc.status}, 같은 도메인 {backoff}초 대기", file=sys.stderr)
        else:
            print(f"[ERROR] {key}: {type(exc).__name__}: {msg}", file=sys.stderr)
        record_events(m, _record_health(state, key, m.get("name", key), m["url"],
                                       error=msg, duration=time.monotonic() - started))
        persist()

    if not dry_run and state.get("pending_notifications"):
        try:
            _flush_notifications(state, state_path)
        except Exception as exc:
            errors += 1
            print(f"[NOTIFY] 이전 알림 재전송 실패: {_error_text(exc)}", file=sys.stderr)

    def check_all(browser=None):
        for m in active:
            host = urlsplit(m["url"]).hostname or ""
            if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
                counts["paused"] += 1
                continue
            started = time.monotonic()
            try:
                html = fetch_html(m, browser)
                previous = state["monitors"].get(m["id"])
                current, events = compare(m, previous, html)
                # 이벤트를 큐에 넣은 뒤 상태를 저장한다. 웹훅 오류로 이벤트가 사라지지 않는다.
                record_events(m, events)
                state["monitors"][m["id"]] = current
                _register_products(state, m, previous, events)
                record_events(m, _record_health(state, m["id"], m.get("name", m["id"]), m["url"],
                                               duration=time.monotonic() - started))
                persist()
                counts["pages"] += 1
                print(f"[OK] {m['id']}: {current.get('status', str(current.get('last_count', len(current.get('regions', [])))))}"
                      f" / 새 알림 {len(events)}건 / {time.monotonic() - started:.1f}초"
                      + (" (dry run, 미전송/미저장)" if dry_run else ""))
            except Exception as exc:
                failed(m, m["id"], exc, started)

    if any(m.get("render", "http") == "browser" for m in active):
        try:
            from playwright.sync_api import sync_playwright
            with sync_playwright() as p:
                browser = p.chromium.launch(headless=True)
                try:
                    check_all(browser)
                finally:
                    browser.close()
        except Exception as exc:
            # 브라우저 설치/시작 실패도 알림 큐 및 상태를 보존한다.
            failed(active[0], "browser", exc, time.monotonic())
    else:
        check_all()

    # 최근 새 상품 우선, 이후 오래 확인하지 않은 상품 순으로 조회한다.
    # 모든 옵션을 한 순회에서 읽지 못하면 scan_queue를 보존하여 이어서 진행한다.
    enabled_sources = {m["id"] for m in active if m.get("track_variants", True)}
    targets = state.get("tracked_products", {})
    candidates = [(key, target) for key, target in targets.items()
                  if any(present and source in enabled_sources
                         for source, present in target.get("sources", {}).items())]
    candidates.sort(key=lambda pair: (not pair[1].get("priority", False),
                                      pair[1].get("last_attempt_at", ""), pair[0]))
    budget = [48]
    with requests.Session() as session:
        for key, target in candidates[:8]:
            if budget[0] < 2:
                break
            host = urlsplit(target["url"]).hostname or ""
            if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
                counts["paused"] += 1
                continue
            m = {"id": "variant-" + hashlib.sha256(key.encode()).hexdigest()[:16],
                 "name": "Chrome Hearts 사이즈 " + target["title"], "url": target["url"]}
            started = time.monotonic()
            target["last_attempt_at"] = _when()
            target["priority"] = False
            try:
                current, events = check_product_variants(session, target, budget)
                record_events(m, events)
                targets[key] = current
                record_events(m, _record_health(state, m["id"], m["name"], m["url"],
                                               duration=time.monotonic() - started))
                persist()
                counts["details"] += 1
                print(f"[VARIANT] {target['pid']}: 저장된 옵션 {len(current['variants'])}개, "
                      f"다음 순회로 넘긴 URL {len(current.get('scan_queue', []))}개 / 새 알림 {len(events)}건")
            except _BudgetExhausted:
                persist()
                break
            except Exception as exc:
                failed(m, m["id"], exc, started)
    if not dry_run:
        try:
            _flush_notifications(state, state_path)
        except Exception as exc:
            errors += 1
            print(f"[NOTIFY] 알림 전송 실패, 미전송 항목 보존: {_error_text(exc)}", file=sys.stderr)
    print(f"총 {counts['pages']}개 페이지 / {counts['details']}개 상세 확인, "
          f"{counts['events']}건 감지, 실패 {errors}개, 접근차단 대기 {counts['paused']}개, "
          f"대기 알림 {len(state.get('pending_notifications', []))}건")
    return 1 if errors or counts["paused"] else 0


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
    git("pull", "--rebase", "origin", branch)
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
    check = check or (lambda: run(config_path, state_path, dry_run=dry_run))
    checkpoint = checkpoint or (lambda: git_checkpoint(state_path))
    started = clock()
    deadline = started + duration_seconds
    iteration = failures = successes = 0
    print(f"[LOOP] 감시 시작: {interval_seconds}초 간격, 최대 {duration_seconds}초, "
          f"Git 동기화={'사용' if git_sync else '미사용'}", flush=True)
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
            print(f"[LOOP] #{iteration} 감시 오류: {type(exc).__name__}: {str(exc)[:180]}",
                  file=sys.stderr, flush=True)
        # Push state even after partial monitor errors: other monitors may have succeeded.
        if git_sync:
            try:
                checkpoint()
            except Exception as exc:
                # subprocess output intentionally omitted; avoid logging access tokens.
                print(f"[STATE] 저장소 동기화 실패 ({type(exc).__name__}). 다음 주기에 재시도합니다.",
                      file=sys.stderr, flush=True)
        remaining = deadline - clock()
        if remaining <= 0:
            break
        next_tick = tick_start + interval_seconds
        pause = min(remaining, max(0.0, next_tick - clock()))
        if pause > 0:
            sleep(pause)
    print(f"[LOOP] 종료: 확인 {iteration}회, 성공 {successes}회, 오류 {failures}회", flush=True)
    return 0 if successes else 1




def probe_site(config_path: Path) -> int:
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
            response = requests.get(url, timeout=20, allow_redirects=True,
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
            elif status in (403, 429):
                line += " | 접근 거부/요청 제한 — 품절이 아니라 차단입니다"
            print(line, flush=True)
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
                        default=int(os.getenv("CHECK_INTERVAL_SECONDS", "60")))
    parser.add_argument("--duration-seconds", type=int,
                        default=int(os.getenv("RUN_DURATION_SECONDS", "21480")))
    args = parser.parse_args()
    if args.probe_site:
        return probe_site(Path(args.config))
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
