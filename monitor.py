#!/usr/bin/env python3
"""크롬하츠(chromehearts.com) 전용 쪽감시자: 신상품 등록, 재입고/판매 시작,
개별 상품 구매 가능(Add to Bag) 전환을 Discord로 알림.

- catalog      : 카테고리 목록 페이지(예: /scents, /socks)를 감시. 신규 상품, 품절→구매가능
                 재입고, (옵션) 구매가능→품절 변경을 상품코드(PID) 기준으로 추적.
- availability : 개별 상품 상세 페이지의 Add to Bag / Sold Out / Coming Soon 상태 감시.
- items/region : 범용 모드(선택자 기반)로 그대로 유지.

로그인 쿠키를 요청하거나 외부 서버에 인증정보를 보내지 않습니다. 403/429/캡차는
우회하지 않고 대기합니다. 기본값은 첫 실행 알림 없음입니다.
"""
from __future__ import annotations

import argparse
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

from bs4 import BeautifulSoup
import requests

STATE_VERSION = 1
CAPTCHA_PHRASES = (
    "verify you are human", "access denied", "checking your browser",
    "unusual traffic", "captcha required", "cloudflare ray id",
)
MAX_SEEN = 10000
MAX_ITEMS = 500

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
        value = normalized(" ".join(e.get_text(" ", strip=True) for e in elements))
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
    return "available"


def extract_catalog(html: str, monitor: dict) -> list[dict]:
    """카테고리 목록에서 상품 링크(PID 포함 *.html)를 찾아 상품별 {pid,key,title,url,price,image,status} 반환.

    CSS 클래스명에 의존하지 않고 '상품 상세 링크 패턴'으로 상품을 식별하므로 사이트의
    마크업이 조금 바뀌어도 동작한다. 타일 안에 라벨이 없으면 구매 가능으로 간주한다.
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
    for _ in range(5):
        if cursor is None or not hasattr(cursor, "attrs"):
            break
        if cursor.has_attr("hidden") or cursor.get("aria-hidden") == "true":
            return False
        style = re.sub(r"\s+", "", str(cursor.get("style", "")).lower())
        if "display:none" in style or "visibility:hidden" in style:
            return False
        if cursor.get("data-pagewatch-visible") == "0":
            return False
        cursor = cursor.parent
    return True


def _status_in_panel(panel) -> tuple[str, str] | None:
    """상품 헤더 가까이에 위치한 CTA 위주로 판단. 본문 및 다른 상품은 제외."""
    controls = panel.select("button, [role='button'], input[type='submit'], input[type='button']")
    labels = []
    for el in controls:
        if not _visible_enough(el):
            continue
        label = normalized(el.get("value", "") if el.name == "input" else el.get_text(" ", strip=True))
        if not label:
            label = normalized(el.get("aria-label", ""))
        if label:
            labels.append(label)
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
        value = normalized(el.get_text(" ", strip=True))
        if len(value) <= 90 and COMING_SOON.search(value):
            return "coming_soon", f"표시: {value[:90]}"
    for label in labels:
        if SOLD_OUT.search(label):
            return "sold_out", f"버튼: {label[:90]}"
    for label in labels:
        if ADD_TO_CART.search(label):
            return "available", f"버튼: {label[:90]}"
    # 판매 버튼은 숨긴 템플릿/관련 상품 때문에 전체 body를 검색하지 않는다.
    for el in panel.find_all(["span", "p", "strong"], limit=90):
        if not _visible_enough(el):
            continue
        value = normalized(el.get_text(" ", strip=True))
        if len(value) <= 90 and SOLD_OUT.search(value):
            return "sold_out", f"표시: {value[:90]}"
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
    if REGION_BLOCK.search(normalized(soup.get_text(" ", strip=True))):
        raise ValueError("'This product is not available in your country' 표시: 실행 환경 국가 제한 가능성")

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
        raise ValueError(f"{m['id']}: mode는 catalog, availability, items 또는 region")
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
    for _ in range(int(m.get("max_load_more", 8))):
        try:
            button = page.locator("button, a, [role=button]").filter(has_text=LOAD_MORE).first
            if button.count() == 0 or not button.is_visible():
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
            # 상품이 더 늘지 않았거나 버튼이 사라짐 = 목록 끝. 지금까지 불러온 목록으로 진행.
            break
    return clicks


def _mark_visibility(page, mode: str) -> None:
    """CSS로 실제 감춰진 버튼/상태 문구는 판단에 쓰지 않도록 표시한다."""
    if mode == "availability":
        page.evaluate("""() => {
          for (const el of document.querySelectorAll('button, [role=button], input[type=submit], input[type=button]')) {
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

def compare(m: dict, previous: dict | None, html: str) -> tuple[dict, list[dict]]:
    """(새 상태, 전송할 신규 이벤트). 부트스트랩 시 기본적으로 전송하지 않음."""
    mode = m.get("mode", "items")
    new = dict(previous or {})
    new["mode"] = mode
    boot = previous is None or previous.get("mode") != mode or not previous.get("initialized", False)
    alert_on_first = bool(m.get("notify_on_first_run", False))
    events = []
    if mode in ("items", "discovery"):
        items = extract_discovery(html, m) if mode == "discovery" else extract_items(html, m)
        if not items and (mode == "discovery" or not bool(m.get("allow_empty", False))):
            raise ValueError("상품이 0개입니다. CSS 선택자/캡차/로그인 여부를 확인하세요")
        saved = dict(previous.get("seen", {}) if previous and not boot else {})
        newcomers = [item for item in items if item["key"] not in saved]
        for item in items:
            if item["key"] not in saved:
                saved[item["key"]] = {"title": item["title"], "url": item["url"]}
        if len(saved) > MAX_SEEN:
            saved = dict(list(saved.items())[-MAX_SEEN:])
        new["seen"] = saved
        # 조회할 때마다 커밋하는 일을 방지: 실제 감시 이력이 변할 때만 상태 갱신
        if boot or saved != (previous or {}).get("seen", {}):
            new["last_count"] = len(items)
            new["updated_at"] = _when()
        if not boot or alert_on_first:
            events = [{"kind": "item", **item} for item in newcomers]
    elif mode == "catalog":
        products = optional_catalog_products(html, m) if m.get("optional_catalog") else extract_catalog(html, m)
        if not products and not m.get("optional_catalog") and not bool(m.get("allow_empty", False)):
            raise ValueError("상품 링크가 0개입니다. 차단/캡차/페이지 구조 변경 여부를 확인하세요")
        saved = dict(previous.get("seen", {}) if previous and not boot else {})
        notify_new = bool(m.get("notify_on_new", True))
        notify_restock = bool(m.get("notify_on_restock", True))
        notify_sold_out = bool(m.get("notify_on_sold_out", False))
        restocks, soldouts, newcomers = [], [], []
        for p in products:
            old = saved.get(p["key"])
            if old is None:
                newcomers.append({"kind": "new_product", **p})
            else:
                old_status = old.get("status", "available")
                if p["status"] != old_status:
                    changed = {**p, "previous_status": old_status}
                    if p["status"] == "available" and old_status in ("sold_out", "coming_soon"):
                        restocks.append({"kind": "restock", **changed})
                    elif p["status"] == "sold_out":
                        soldouts.append({"kind": "sold_out", **changed})
            saved[p["key"]] = {"title": p["title"], "url": p["url"], "status": p["status"]}
        if len(saved) > MAX_SEEN:
            saved = dict(list(saved.items())[-MAX_SEEN:])
        new["seen"] = saved
        # 가격만 변하거나 순서가 바뀌는 것은 상태 변경으로 보지 않는다(불필요한 커밋 방지).
        if boot or saved != (previous or {}).get("seen", {}):
            new["last_count"] = len(products)
            new["updated_at"] = _when()
        if not boot or alert_on_first:
            if notify_restock:
                events += restocks
            if notify_new:
                events += newcomers
            if notify_sold_out:
                events += soldouts
    elif mode == "availability":
        result = detect_availability(html, m)
        status = result["status"]
        old_status = previous.get("status") if previous and not boot else None
        new["status"] = status
        new["title"] = result["title"]
        new["sku"] = result["sku"]
        if boot or status != old_status:
            new["updated_at"] = _when()
        # 첫 실행이 이미 구매 가능하면 알림(옵션). Coming Soon에는 보내지 않는다.
        if status == "available" and (old_status != "available") and (not boot or alert_on_first):
            events = [{"kind": "availability", "status": status, "previous_status": old_status,
                       "title": result["title"], "sku": result["sku"], "url": result["url"],
                       "evidence": result["evidence"]}]
        elif status != "available" and bool(m.get("notify_on_unavailable", False)) and \
                old_status != status and (not boot or alert_on_first):
            events = [{"kind": "availability", "status": status, "previous_status": old_status,
                       "title": result["title"], "sku": result["sku"], "url": result["url"],
                       "evidence": result["evidence"]}]
    else:
        regions = extract_regions(html, m)
        old_regions = previous.get("regions", []) if previous and not boot else []
        new["regions"] = regions
        if boot or regions != old_regions:
            new["updated_at"] = _when()
        if not boot or alert_on_first:
            for index, after in enumerate(regions):
                before = old_regions[index] if index < len(old_regions) else ""
                if before != after:
                    events.append({"kind": "region", "selector": m["region_selectors"][index],
                                   "before": before[:350], "after": after[:550]})
    new["initialized"] = True
    return new, events


def _discord_url() -> str:
    url = os.environ.get("DISCORD_WEBHOOK_URL", "").strip()
    p = urlsplit(url)
    if p.scheme != "https" or p.hostname not in ("discord.com", "discordapp.com") or not re.fullmatch(
        r"/api(?:/v\d+)?/webhooks/\d+/[A-Za-z0-9_-]+/?", p.path
    ) or p.query or p.fragment:
        raise ValueError("DISCORD_WEBHOOK_URL에 정상적인 Discord 웹훅 URL을 GitHub Secret으로 설정하세요")
    return url


def send_discord(m: dict, events: list[dict]) -> None:
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
    for start in range(0, len(events), limit):
        batch = events[start:start + limit]
        descriptions = []
        for e in batch:
            if e["kind"] in ("new_product", "restock", "sold_out"):
                title = e["title"].replace("`", "′").replace("[", "［").replace("]", "］")[:170]
                head = {"new_product": "🆕 신상품 등록", "restock": "🔄 재입고/구매 가능",
                        "sold_out": "⛔ 품절"}[e["kind"]]
                desc = f"• {head}: **{title}**\n  상품코드: `{e['pid']}`"
                if e.get("price"):
                    desc += f"\n  가격: {e['price']}"
                if e["kind"] == "new_product":
                    desc += f"\n  상태: {AVAILABILITY_LABELS.get(e['status'], e['status'])}"
                else:
                    desc += (f"\n  상태 변화: {AVAILABILITY_LABELS.get(e.get('previous_status'), '확인 불가')}"
                             f" → **{AVAILABILITY_LABELS.get(e['status'], e['status'])}**")
                if e.get("url"):
                    desc += f"\n  {e['url']}"
            elif e["kind"] == "item":
                title = e["title"].replace("`", "′").replace("[", "［").replace("]", "］")[:170]
                product_url = e.get("url", "")
                desc = f"• **{title}**"
                if product_url:
                    desc += f" — {product_url}"
                if e.get("price"):
                    desc += f"\n  가격: {e['price']}"
            elif e["kind"] == "availability":
                status_text = AVAILABILITY_LABELS.get(e["status"], e["status"])
                prev = AVAILABILITY_LABELS.get(e.get("previous_status"), "최초 확인")
                title = e["title"].replace("`", "′").replace("[", "［").replace("]", "］")[:160]
                desc = (f"• **{title}**\n  상품코드: `{e['sku']}`\n"
                        f"  상태 변화: {prev} → **{status_text}**\n"
                        f"  근거: {e['evidence']}\n  {e['url']}")
            else:
                desc = f"• **{e['selector']}** 영역 변경\n  변경 전: {e['before'][:250]}\n  변경 후: {e['after'][:400]}"
            descriptions.append(desc[:850])
        remainder = len(events) - start - len(batch)
        if remainder and remainder < 30 and start + limit >= len(events):
            descriptions.append(f"추가 감지: {remainder}건")
        embed = {"title": f"{m.get('name', m['id'])} 변경 알림"[:240],
                 "description": "\n\n".join(descriptions)[:3900],
                 "url": m["url"], "color": 0xC0C0C0}
        thumb = next((e.get("image", "") for e in batch if str(e.get("image", "")).startswith("https://")), "")
        if thumb:
            embed["thumbnail"] = {"url": thumb}
        payload = {
            "content": (mention + f"🔔 {m.get('name', m['id'])}: 상태 변경/신규 물품 {len(batch)}건 감지")[:1900],
            "embeds": [embed],
            "allowed_mentions": mentions,
        }
        for retry in range(4):
            r = requests.post(url, json=payload, timeout=20, allow_redirects=False)
            if r.status_code in (200, 204):
                break
            if r.status_code == 429 and retry < 3:
                try:
                    wait = min(15, max(1.0, float(r.json().get("retry_after", 2))))
                except (ValueError, AttributeError, TypeError):
                    wait = 2
                time.sleep(wait)
                continue
            if r.status_code >= 500 and retry < 3:
                time.sleep(retry + 1)
                continue
            raise RuntimeError(f"Discord 전송 실패: HTTP {r.status_code}")
        else:
            raise RuntimeError("Discord 요청 한도 초과")


def run(config_path: Path, state_path: Path, *, dry_run: bool = False) -> int:
    config = json.loads(config_path.read_text(encoding="utf-8"))
    monitors = config.get("monitors", [])
    if not isinstance(monitors, list):
        raise ValueError("config의 monitors는 배열이어야 합니다")
    active = [m for m in monitors if m.get("enabled", False)]
    if not active:
        print("[설정 필요] enabled=true인 감시 대상이 없습니다. config/monitors.json을 편집하세요.")
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
    counts = {"events": 0, "pages": 0, "paused": 0}

    def check_all(browser=None):
        nonlocal errors
        for m in active:
            host = urlsplit(m["url"]).hostname or ""
            if time.monotonic() < _SITE_BLOCKED_UNTIL.get(host, 0):
                counts["paused"] += 1
                continue
            try:
                html = fetch_html(m, browser)
                previous = state["monitors"].get(m["id"])
                current, events = compare(m, previous, html)
                if events and not dry_run:
                    send_discord(m, events)
                if not dry_run and current != previous:
                    state["monitors"][m["id"]] = current
                    save_state(state_path, state)
                counts["pages"] += 1
                counts["events"] += len(events)
                summary = (f"판매 상태={current.get('status')}" if m.get("mode") == "availability"
                           else f"{current.get('last_count',len(current.get('regions', [])))}개 확인")
                print(f"[OK] {m['id']}: {summary} / 새 알림 {len(events)}건"
                      + (" (dry run, 미전송)" if dry_run else ""))
            except SiteAccessDenied as exc:
                errors += 1
                backoff = _block_backoff_seconds()
                _SITE_BLOCKED_UNTIL[host] = time.monotonic() + backoff
                print(f"[BLOCKED] {m['id']}: HTTP {exc.status}, {host} 접속 거부. "
                      f"같은 도메인 재요청을 {backoff}초 중단합니다. "
                      "다른 실행 환경/허용된 공식 접근 방법을 확인하세요.",
                      file=sys.stderr, flush=True)
            except Exception as exc:
                errors += 1
                # 특히 웹훅 토큰은 네트워크 예외 메시지에 섞일 수 있으므로 로그에서 제거.
                msg = str(exc)
                webhook = os.getenv("DISCORD_WEBHOOK_URL", "").strip()
                if webhook:
                    msg = msg.replace(webhook, "<redacted-webhook>")
                    path = urlsplit(webhook).path
                    if path:
                        msg = msg.replace(path, "<redacted-webhook-path>")
                msg = re.sub(r"(/api(?:/v\d+)?/webhooks/\d+/)[A-Za-z0-9_-]+", r"\1<redacted>", msg)
                print(f"[ERROR] {m.get('id', '?')}: {type(exc).__name__}: {msg[:180]}", file=sys.stderr)

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
            print(f"[ERROR] 브라우저 시작 실패: {type(exc).__name__}: {str(exc)[:180]}", file=sys.stderr)
            return 1
    else:
        check_all()
    print(f"총 {counts['pages']}개 페이지 확인, {counts['events']}건 감지, "
          f"실패 {errors}개, 접근차단 대기 {counts['paused']}개")
    # 대기 상태를 성공으로 취급하지 않는다. 알림 감시가 정상 작동 중이라는 착각을 방지.
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
