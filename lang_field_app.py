"""
lang_field_app.py
────────────────────────────────────────────────────────
041(언어코드) · 546(언어주기) 필드 단독 테스트 앱
ISBN 입력 → 알라딘 API 자동 조회 → 필드 생성
────────────────────────────────────────────────────────
"""

import os
import re
import json
import html
import time
import requests
from bs4 import BeautifulSoup

import streamlit as st
from openai import OpenAI
from lang_field import LangFieldBuilder, ISDS_LANGUAGE_CODES

# ── 페이지 설정 ──────────────────────────────────────
st.set_page_config(
    page_title="041 · 546 필드 생성기",
    page_icon="📚",
    layout="centered",
)

st.title("📚 KORMARC 041 · 546 필드 생성기")
st.caption("ISBN을 입력하면 도서 정보를 자동으로 불러와 언어코드(041)와 언어주기(546) 필드를 생성합니다.")

# ── Secrets / 환경변수 ───────────────────────────────
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY") or st.secrets.get("OPENAI_API_KEY", "")
ALADIN_TTB_KEY = (
    os.getenv("ALADIN_TTB_KEY")
    or st.secrets.get("ALADIN_TTB_KEY", "")
    or (st.secrets.get("aladin") or {}).get("ttbkey", "")
)

if not OPENAI_API_KEY:
    st.error("⚠️ OPENAI_API_KEY가 설정되지 않았습니다. Streamlit Secrets에 등록해주세요.")
    st.stop()

client = OpenAI(api_key=OPENAI_API_KEY)

# ── 디버그 로그 수집 ──────────────────────────────────
debug_lines: list[str] = []
def dbg(*args):
    debug_lines.append(" ".join(str(a) for a in args))
def dbg_err(*args):
    debug_lines.append("❌ " + " ".join(str(a) for a in args))

builder = LangFieldBuilder(
    openai_client=client,
    model=(st.secrets.get("openai", {}) or {}).get("model", "gpt-4o-mini"),
    dbg_fn=dbg,
    dbg_err_fn=dbg_err,
)


# ══════════════════════════════════════════════════════
# 알라딘 조회 함수
# ══════════════════════════════════════════════════════
def aladin_lookup(isbn13: str) -> dict | None:
    """알라딘 TTB API로 도서 정보 조회. 실패 시 None."""
    if not ALADIN_TTB_KEY:
        return None
    try:
        params = {
            "ttbkey":    ALADIN_TTB_KEY,
            "itemIdType": "ISBN13",
            "ItemId":    isbn13,
            "output":    "js",
            "Version":   "20131101",
            "OptResult": "authors,categoryIdList,fulldescription,Story,toc",
        }
        r = requests.get(
            "https://www.aladin.co.kr/ttb/api/ItemLookUp.aspx",
            params=params, timeout=10,
        )
        data  = r.json()
        items = data.get("item", [])
        return items[0] if items else None
    except Exception as e:
        dbg_err(f"알라딘 API 오류: {e}")
        return None


def aladin_crawl(isbn13: str) -> dict:
    """알라딘 상세 페이지 크롤링 — 원제·원어저자·카테고리 보완."""
    url = f"https://www.aladin.co.kr/shop/wproduct.aspx?ISBN={isbn13}"
    try:
        soup = BeautifulSoup(
            requests.get(url, headers={"User-Agent": "Mozilla/5.0"}, timeout=10).text,
            "html.parser",
        )
        original_title = original_author = category_text = ""
        subject_lang   = None

        orig_el = soup.select_one("div.info_original")
        if orig_el:
            original_title = orig_el.text.strip()

        for cat in soup.select("div.conts_info_list2 li"):
            category_text += cat.get_text(separator=" ", strip=True) + " "

        lang_info = soup.select_one("div.conts_info_list1")
        if lang_info and "언어" in lang_info.text:
            if "Japanese" in lang_info.text:  subject_lang = "jpn"
            elif "Chinese" in lang_info.text: subject_lang = "chi"
            elif "English" in lang_info.text: subject_lang = "eng"

        for script in soup.find_all("script", type="application/ld+json"):
            try:
                data = json.loads(script.string or "")
            except Exception:
                continue
            if not (isinstance(data, dict) and data.get("@type") == "Book"):
                continue
            author_data = data.get("author")
            name_field  = ""
            if isinstance(author_data, dict):
                name_field = author_data.get("name", "") or ""
            elif isinstance(author_data, list):
                name_field = ", ".join(
                    a.get("name", "") for a in author_data if isinstance(a, dict)
                )
            parts = [p.strip() for p in name_field.split(",") if p.strip()]
            if len(parts) >= 2:
                cand = parts[1]
                if not re.search(r"[가-힣]", cand):
                    original_author = cand

        return {
            "original_title":  original_title,
            "original_author": original_author,
            "category_text":   category_text.strip(),
            "subject_lang":    subject_lang,
        }
    except Exception as e:
        dbg_err(f"크롤링 오류: {e}")
        return {}


# ══════════════════════════════════════════════════════
# UI
# ══════════════════════════════════════════════════════
st.divider()

isbn_input = st.text_input(
    "📖 ISBN-13 입력",
    placeholder="예: 9788937462849",
    max_chars=13,
)

fetch_btn = st.button("🔎 도서 정보 불러오기", use_container_width=True)

# ── ISBN 조회 ─────────────────────────────────────────
if fetch_btn and isbn_input:
    isbn = isbn_input.strip().replace("-", "")
    if len(isbn) != 13 or not isbn.isdigit():
        st.error("ISBN-13은 숫자 13자리여야 합니다.")
        st.stop()

    with st.spinner("알라딘에서 도서 정보 조회 중…"):
        api_item  = aladin_lookup(isbn)
        crawl_det = aladin_crawl(isbn)

    if not api_item and not crawl_det:
        st.error("도서 정보를 찾을 수 없습니다. ISBN을 확인해주세요.")
        st.stop()

    st.session_state["api_item"]  = api_item  or {}
    st.session_state["crawl_det"] = crawl_det or {}
    st.session_state["isbn"]      = isbn

# ── 도서 정보 표시 & 수정 폼 ──────────────────────────
if "api_item" in st.session_state:
    item   = st.session_state["api_item"]
    detail = st.session_state["crawl_det"]

    subinfo        = (item.get("subInfo") or {}) or {}
    orig_from_api  = html.unescape(subinfo.get("originalTitle", "") or "")

    st.divider()
    st.subheader("📋 불러온 도서 정보")

    cover = item.get("cover", "")
    if cover:
        col_img, col_info = st.columns([1, 3])
        with col_img:
            st.image(cover, width=110)
        with col_info:
            st.markdown(f"**{item.get('title', '')}**")
            st.caption(
                f"{item.get('author', '')}  |  "
                f"{item.get('publisher', '')}  |  "
                f"{(item.get('pubDate', '') or '')[:4]}"
            )
    else:
        st.markdown(f"**{item.get('title', '')}**")
        st.caption(
            f"{item.get('author', '')}  |  "
            f"{item.get('publisher', '')}  |  "
            f"{(item.get('pubDate', '') or '')[:4]}"
        )

    st.divider()
    st.subheader("✏️ 정보 확인 · 수정 후 필드 생성")
    st.caption("자동으로 채워진 값을 확인하고 필요하면 수정하세요.")

    col1, col2 = st.columns(2)
    with col1:
        title     = st.text_input("제목",   value=item.get("title", ""))
        publisher = st.text_input("출판사", value=item.get("publisher", ""))
        author    = st.text_input("저자",   value=item.get("author", ""))
    with col2:
        original_title = st.text_input(
            "원제",
            value=orig_from_api or detail.get("original_title", ""),
        )
        category_text  = st.text_input(
            "카테고리",
            value=item.get("categoryText", "") or detail.get("category_text", ""),
        )
        subject_lang   = st.text_input(
            "언어 힌트 (선택)",
            value=detail.get("subject_lang", "") or "",
            placeholder="예: rus  (크롤링 자동감지)",
        )

    run_btn = st.button("🚀 041 · 546 필드 생성", type="primary", use_container_width=True)

    if run_btn:
        debug_lines.clear()

        final_item = {
            "title":        title,
            "publisher":    publisher,
            "author":       author,
            "categoryText": category_text,
            "itemId":       item.get("itemId") or item.get("item_id") or "",
            "isbn13":       item.get("isbn13") or item.get("isbn") or "",
            "subInfo": {
                **(item.get("subInfo") or {}),
                "originalTitle": original_title,
            },
        }
        final_detail = {
            "original_title": original_title,
            "subject_lang":   subject_lang or None,
            "category_text":  category_text,
        }

        with st.spinner("언어 판정 중…"):
            _t0 = time.perf_counter()
            tag_041, tag_546, orig = builder.get_kormarc_tags(final_item, final_detail)
            _elapsed = time.perf_counter() - _t0

        st.divider()
        st.subheader("✅ 생성 결과")
        st.caption(f"⏱️ 판정 소요 시간: **{_elapsed:.2f}초**")

        if tag_041 and "$h" in tag_041:
            mrk_041 = builder.as_mrk_041(tag_041)
            mrk_546 = builder.as_mrk_546(tag_546)

            col_a, col_b = st.columns(2)
            with col_a:
                st.markdown("**041 언어코드 필드**")
                st.code(mrk_041 or tag_041, language="text")
            with col_b:
                st.markdown("**546 언어주기 필드**")
                st.code(mrk_546 or tag_546 or "(없음)", language="text")

            h_code = builder.extract_lang_h(tag_041)
            a_code = builder.lang3_from_tag041(tag_041)
            st.info(
                f"📖 본문 언어: **{ISDS_LANGUAGE_CODES.get(a_code or '', '?')}** (`{a_code}`)"
                f"　　원서 언어: **{ISDS_LANGUAGE_CODES.get(h_code or '', '?')}** (`{h_code}`)"
            )
            if orig:
                st.caption(f"원제: {orig}")

        elif tag_041 and tag_041.startswith("📕"):
            st.error(tag_041)

        else:
            lang_a = builder.detect_language(title)
            if builder.is_domestic_category(category_text):
                lang_a = "kor"
            st.success("✅ 번역서가 아닌 것으로 판정 — 041 · 546 필드를 생성하지 않습니다.")
            st.info(
                f"📖 본문 언어 추정: **{ISDS_LANGUAGE_CODES.get(lang_a, '?')}** (`{lang_a}`)"
            )

        with st.expander("🧭 판정 로그 보기"):
            st.text("\n".join(debug_lines) if debug_lines else "로그 없음")

elif not fetch_btn:
    st.info("ISBN-13을 입력하고 '도서 정보 불러오기' 버튼을 눌러주세요.")

# ── 알라딘 키 없을 때 안내 ────────────────────────────
if not ALADIN_TTB_KEY:
    st.warning(
        "⚠️ ALADIN_TTB_KEY가 없어 API 자동조회가 제한됩니다. "
        "Secrets에 등록하면 도서 정보를 자동으로 불러올 수 있습니다."
    )
