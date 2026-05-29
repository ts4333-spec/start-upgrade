"""
lang_field_integrated.py
────────────────────────────────────────────────────────────────────────────
KORMARC 041(언어코드) · 546(언어주기) 필드 생성 — 통합 모듈

【구조】
  AladinTools      — 알라딘 API/크롤링 공통 유틸
                     (ItemLookUp, ItemSearch, Bio 수집, 원제/AuthorId 보완)
  BioAnalyzer      — Bio 텍스트 분석 순수 함수
                     (전공 추출, 문자 체계 가중치, 커리어 힌트 집계)
  LangFieldBuilder — 메인 파이프라인 오케스트레이터
                     · 단계 1: $a 본문 언어 판정
                     · 단계 2: 문학/비문학 카테고리 분류
                     · 단계 3: $h 원서 언어 파이프라인
                         - 분기A(문학): Rule → GPT-General → GPT-Author
                         - 분기B(비문학): Bio 수집 → FastTrack 분석 →
                           [GPT 있으면] 하이브리드 단일 호출 →
                           [SafeTrack: confidence=low 시] 역자 커리어 →
                           Rule 폴백
                     · 단계 4: 충돌 조정 → 041/546 태그 생성

【사용 예시】
    from lang_field_integrated import LangFieldBuilder

    builder = LangFieldBuilder(
        openai_client=client,   # OpenAI() 인스턴스 또는 None
        ttbkey="TTBxxx",        # 알라딘 TTB 키 (커리어 검색용, 없어도 동작)
        model="gpt-4o",
        dbg_fn=dbg,
        dbg_err_fn=dbg_err,
    )
    tag_041, tag_546, orig_title = builder.get_kormarc_tags(item, detail)
────────────────────────────────────────────────────────────────────────────
"""
from __future__ import annotations

import html as _html_stdlib
import json
import re
import time
import urllib.error
import urllib.request
from collections import defaultdict
from typing import Any, Callable, Dict, List, Mapping, Optional, Tuple

try:
    import requests
    from bs4 import BeautifulSoup
    _SCRAPER_AVAILABLE = True
except ImportError:
    _SCRAPER_AVAILABLE = False


# ═══════════════════════════════════════════════════════════════
# 1. 전역 상수
# ═══════════════════════════════════════════════════════════════

ISDS_LANGUAGE_CODES: Dict[str, str] = {
    "kor": "한국어",  "eng": "영어",    "jpn": "일본어",   "chi": "중국어",
    "rus": "러시아어","ara": "아랍어",  "fre": "프랑스어", "ger": "독일어",
    "ita": "이탈리아어", "spa": "스페인어", "por": "포르투갈어", "tur": "터키어",
    "und": "알 수 없음",
}
ALLOWED_CODES: frozenset = frozenset(ISDS_LANGUAGE_CODES.keys()) - {"und"}

# 언어 이름(한국어) → ISDS 코드
_LANG_NAME_TO_ISDS: Dict[str, str] = {
    "영어": "eng", "일본어": "jpn", "중국어": "chi", "러시아어": "rus",
    "프랑스어": "fre", "독일어": "ger", "이탈리아어": "ita",
    "스페인어": "spa", "포르투갈어": "por", "터키어": "tur", "한국어": "kor",
    "아랍어": "ara",
}

# 알라딘 API 엔드포인트
_ITEM_LOOKUP_URL = "http://www.aladin.co.kr/ttb/api/ItemLookUp.aspx"
_ITEM_SEARCH_URL = "http://www.aladin.co.kr/ttb/api/ItemSearch.aspx"
_WAUTHOR_OVERVIEW_URL = "https://www.aladin.co.kr/author/wauthor_overview.aspx"
_WPRODUCT_URL = "https://www.aladin.co.kr/shop/wproduct.aspx"
_API_VERSION = "20131101"
_OPT_LOOKUP = "authors,categoryIdList,fulldescription,Story,toc"

_WEB_HEADERS: Dict[str, str] = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8",
    "Referer": "https://www.aladin.co.kr/",
}

# wauthor_overview HTML 정제 시 제거할 태그
_BIO_DECOMPOSE_TAGS: Tuple[str, ...] = (
    "script", "style", "meta", "noscript", "header", "footer",
    "nav", "aside", "menu", "form", "button", "input", "select",
    "label", "iframe", "link", "ul", "ol", "li", "a",
)

# 역자 역할 키워드
_TRANSLATOR_ROLE_KEYS: Tuple[str, ...] = ("옮긴이", "역자", "옮김", "번역")
_WRITER_ROLE_KEYS: Tuple[str, ...] = ("지은이", "지음", "글")

# API Bio 필드 우선순위
_API_BIO_KEYS: Tuple[str, ...] = (
    "authorBio", "biography", "authorIntro",
    "intro", "description", "authorDescription", "profile",
)
_ITEM_DESC_KEYS: Tuple[str, ...] = (
    "fulldescription", "fullDescription", "Story", "story", "toc", "Toc",
)

# 문자 체계 정규식
_RE_KANA  = re.compile(r"[\u3040-\u309F\u30A0-\u30FF]")
_RE_HAN   = re.compile(r"[\u4E00-\u9FFF]")
_RE_LATIN = re.compile(r"[A-Za-z]")

# 전공 → 언어 규칙
_MAJOR_LANG_RULES: List[Tuple[str, str]] = [
    (r"노어|러시아|슬라브",           "러시아어"),
    (r"영미|영어|미국문학|영문",       "영어"),
    (r"불어|프랑스",                   "프랑스어"),
    (r"독어|독일",                     "독일어"),
    (r"스페인|스페인어|히스패닉",      "스페인어"),
    (r"이탈리아|이태리",               "이탈리아어"),
    (r"일본|일어",                     "일본어"),
    (r"중국|중문|한문|중어",           "중국어"),
    (r"아랍|터키|페르시아|이란",       "아랍어권·중동어권"),
    (r"노르웨이|스웨덴|덴마크|북유럽", "북유럽어권"),
    (r"라틴아메리카|포르투갈|브라질",  "포르투갈어"),
    (r"한국어|국어국문",               "한국어"),
]

# 커리어 힌트 레이블 → 언어 이름 매핑
_CAREER_HINT_LANG_MAP: Dict[str, str] = {
    "원제_가나(일본어)":          "일본어",
    "원제_한자(중국어)":          "중국어",
    "원제_한자(일본어)":          "일본어",
    "원제_라틴(영미·유럽권)":     "영어",
    "원제_라틴_보조(영어 가능)":  "영어",
    "메타_영어권":                "영어",
    "메타_일본":                  "일본어",
    "메타_중국":                  "중국어",
    "메타_프랑스":                "프랑스어",
    "메타_독일":                  "독일어",
    "메타_스페인":                "스페인어",
    "메타_이탈리아":              "이탈리아어",
    "메타_러시아":                "러시아어",
    "메타_한국":                  "한국어",
}

# AuthorSearch href ID 추출 정규식
_AUTHOR_SEARCH_HREF_RE = re.compile(r"AuthorSearch=(?:[^&]*?@)?(\d+)", re.I)

# 원제 라벨 집합
_ORIGINAL_TITLE_LABELS = frozenset({"원제", "Original Title", "原題", "原题"})


# ═══════════════════════════════════════════════════════════════
# 2. AladinTools — HTTP/크롤링/API 공통 유틸
# ═══════════════════════════════════════════════════════════════

class AladinTools:
    """
    알라딘 API/웹 크롤링 공통 유틸리티.

    Parameters
    ----------
    ttbkey : 알라딘 TTB API 키. 없으면 API 호출 기능 비활성화.
    timeout : HTTP 타임아웃 (초). 기본 12.
    retry   : GET 실패 시 재시도 횟수. 기본 2.
    """

    def __init__(
        self,
        ttbkey: str = "",
        timeout: int = 12,
        retry: int = 2,
    ):
        self._ttbkey  = (ttbkey or "").strip()
        self._timeout = timeout
        self._retry   = retry

    # ── 공통 HTTP ─────────────────────────────────────────────

    def _get(
        self,
        url: str,
        params: Optional[Dict] = None,
        headers: Optional[Dict] = None,
    ) -> Optional["requests.Response"]:
        """재시도 포함 GET. 실패 시 None."""
        if not _SCRAPER_AVAILABLE:
            return None
        hdrs = headers or _WEB_HEADERS
        for attempt in range(self._retry):
            try:
                resp = requests.get(url, params=params, headers=hdrs, timeout=self._timeout)
                resp.raise_for_status()
                return resp
            except Exception:
                if attempt < self._retry - 1:
                    time.sleep(0.8)
        return None

    def _get_json(self, url: str, params: Dict) -> Optional[Dict]:
        """JSON API GET. 실패 시 None."""
        resp = self._get(url, params=params)
        if resp is None:
            return None
        try:
            return resp.json()
        except Exception:
            return None

    # ── 알라딘 TTB API ────────────────────────────────────────

    def item_lookup(
        self,
        isbn_or_item_id: str,
        item_id_type: str = "ISBN13",
        opt_result: str = _OPT_LOOKUP,
    ) -> Optional[Dict]:
        """ItemLookUp API. ttbkey 없으면 None."""
        if not self._ttbkey:
            return None
        data = self._get_json(_ITEM_LOOKUP_URL, {
            "ttbkey": self._ttbkey,
            "itemIdType": item_id_type,
            "ItemId": isbn_or_item_id,
            "output": "js",
            "Version": _API_VERSION,
            "OptResult": opt_result,
        })
        return data

    def item_search_by_author(
        self,
        author_name: str,
        max_results: int = 50,
    ) -> List[Dict]:
        """역자명으로 ItemSearch (커리어 수집용). 결과 item 목록 반환."""
        if not self._ttbkey or not author_name.strip():
            return []
        data = self._get_json(_ITEM_SEARCH_URL, {
            "ttbkey": self._ttbkey,
            "QueryType": "Author",
            "Query": author_name.strip(),
            "MaxResults": str(max_results),
            "start": "1",
            "SearchTarget": "Book",
            "output": "js",
            "Version": _API_VERSION,
            "OptResult": "authors",
        })
        return (data or {}).get("item") or []

    # ── 상품 상세 페이지 HTML ─────────────────────────────────

    def fetch_product_html(self, item: Dict) -> Optional[str]:
        """
        item dict 에서 ItemId 또는 isbn13 을 추출해
        wproduct 상세 페이지 HTML 을 반환. 실패 시 None.
        """
        pid = self._product_item_id(item)
        if not pid:
            return None
        resp = self._get(_WPRODUCT_URL, params={"ItemId": pid})
        return resp.text if resp else None

    @staticmethod
    def _product_item_id(item: Dict) -> Optional[str]:
        """itemId > item_id > isbn13 > isbn 순으로 ItemId 결정."""
        for key in ("itemId", "item_id"):
            v = item.get(key)
            if v is not None and str(v).strip():
                return str(v).strip()
        isbn = (item.get("isbn13") or item.get("isbn") or "").replace("-", "").strip()
        return isbn or None

    # ── AuthorId 추출 ─────────────────────────────────────────

    @staticmethod
    def extract_id_from_href(href: str) -> Optional[int]:
        """href 에서 AuthorSearch=…@숫자 패턴으로 ID 추출."""
        if not href or "AuthorSearch=" not in href:
            return None
        m = _AUTHOR_SEARCH_HREF_RE.search(href)
        if not m:
            return None
        try:
            return int(m.group(1))
        except (TypeError, ValueError):
            return None

    def resolve_author_id_from_html(self, html: str, target_name: str) -> Optional[int]:
        """
        상품 상세 HTML 에서 AuthorSearch= 링크를 순회하며
        앵커 텍스트가 target_name 과 일치하는 항목의 ID 반환.
        """
        if not _SCRAPER_AVAILABLE or not html or not target_name.strip():
            return None
        soup = BeautifulSoup(html, "html.parser")
        t = target_name.strip()
        for anchor in soup.find_all("a", href=True):
            href = anchor.get("href") or ""
            if "AuthorSearch=" not in href:
                continue
            text = re.sub(r"\s+", " ", anchor.get_text(separator=" ", strip=True)).strip()
            if text != t:
                continue
            aid = self.extract_id_from_href(href)
            if aid is not None:
                return aid
        return None

    # ── Bio 수집 ──────────────────────────────────────────────

    def collect_bio_from_api(self, item: Dict, target_name: str) -> str:
        """
        subInfo.authors 에서 target_name 의 Bio 필드를 수집.
        item 루트의 fulldescription/Story 등도 보조 포함.
        """
        chunks: List[str] = []
        sub = item.get("subInfo") or {}
        for auth in sub.get("authors") or []:
            if not isinstance(auth, dict):
                continue
            if target_name:
                api_name = (auth.get("authorName") or "").strip()
                if api_name != target_name.strip():
                    continue
            for key in _API_BIO_KEYS:
                val = auth.get(key)
                if isinstance(val, str) and val.strip():
                    chunks.append(val.strip())
            for k, v in auth.items():
                if k in ("authorName", "authorId", "authorTypeDesc", "authorTypeName"):
                    continue
                if isinstance(v, str) and len(v) > 40:
                    chunks.append(v.strip())
        for key in _ITEM_DESC_KEYS:
            v = item.get(key) or sub.get(key)
            if isinstance(v, str) and len(v) > 80:
                chunks.append(v[:5000])
        return "\n\n".join(dict.fromkeys(chunks))

    def scrape_bio_from_overview(self, author_id: int) -> str:
        """
        wauthor_overview.aspx 에서 소개글 크롤링.
        노이즈 태그 제거 후 p·리프 div 에서 텍스트 수집.
        """
        if not _SCRAPER_AVAILABLE or not author_id:
            return ""
        resp = self._get(_WAUTHOR_OVERVIEW_URL, params={"AuthorSearch": f"@{author_id}"})
        if resp is None:
            return ""
        soup = BeautifulSoup(resp.text, "html.parser")
        for tag in _BIO_DECOMPOSE_TAGS:
            for el in soup.find_all(tag):
                el.decompose()
        root = soup
        for attr, pat in (
            ("id",    re.compile(r"author|writer|profile|bio", re.I)),
            ("class", re.compile(r"author|writer|profile|bio|intro", re.I)),
        ):
            found = soup.find(attrs={attr: pat})
            if found is not None:
                root = found
                break
        chunks: List[str] = []
        for p in root.find_all("p"):
            t = p.get_text(separator=" ", strip=True)
            if len(t) >= 8:
                chunks.append(t)
        for div in root.find_all("div"):
            if div.find(["div", "p", "ul", "ol", "nav", "table"]):
                continue
            t = div.get_text(separator=" ", strip=True)
            if len(t) >= 20:
                chunks.append(t)
        bio = "\n\n".join(dict.fromkeys(chunks))
        if not bio and root is not soup:
            for p in soup.find_all("p"):
                t = p.get_text(separator=" ", strip=True)
                if len(t) >= 8:
                    chunks.append(t)
            bio = "\n\n".join(dict.fromkeys(chunks))
        return bio[:1500] if bio else ""

    def fetch_single_bio(
        self,
        item: Dict,
        names: List[str],
        want_translator: bool,
        product_html_cache: Optional[str] = None,
    ) -> str:
        """
        Step 1: API Bio
        Step 2: API authorId → wauthor_overview 크롤링
        Step 3: authorId 없으면 상품 HTML 에서 ID 파싱 → 크롤링
        """
        cached_html: Optional[str] = product_html_cache
        for name in names[:2]:
            # Step 1
            api_bio = self.collect_bio_from_api(item, name)
            if api_bio.strip() and len(api_bio.strip()) > 5:
                return api_bio.strip()
            if not _SCRAPER_AVAILABLE:
                continue
            # Step 2
            aid = self._extract_id_from_api(item, name, want_translator)
            # Step 3
            if aid is None:
                if cached_html is None:
                    cached_html = self.fetch_product_html(item)
                if cached_html:
                    aid = self.resolve_author_id_from_html(cached_html, name)
            if aid is None:
                continue
            web_bio = self.scrape_bio_from_overview(aid)
            if web_bio.strip():
                return web_bio.strip()
        return ""

    @staticmethod
    def _extract_id_from_api(item: Dict, target_name: str, want_translator: bool) -> Optional[int]:
        """subInfo.authors 에서 역할+이름 일치하는 authorId 반환."""
        sub = item.get("subInfo") or {}
        for auth in sub.get("authors") or []:
            if not isinstance(auth, dict):
                continue
            api_name = (auth.get("authorName") or "").strip()
            if target_name and api_name != target_name.strip():
                continue
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if want_translator and not _is_translator_role(role):
                continue
            if not want_translator and not _is_writer_role(role):
                continue
            aid = auth.get("authorId")
            try:
                return int(aid) if aid is not None else None
            except (TypeError, ValueError):
                return None
        return None

    def fetch_bios(self, item: Dict) -> Tuple[str, str]:
        """
        item 으로부터 (author_bio, translator_bio) 를 한 번에 수집.
        저자·역자 이름 목록을 결정하고 fetch_single_bio 에 위임.
        """
        item = item or {}
        sub = item.get("subInfo") or {}
        authors_list = [a for a in (sub.get("authors") or []) if isinstance(a, dict)]

        writer_names: List[str] = []
        for auth in authors_list:
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _is_writer_role(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    writer_names.append(n)
        if not writer_names:
            writer_names = _parse_names_from_raw(item.get("author") or "", want_translator=False)

        translator_names: List[str] = []
        for auth in authors_list:
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _is_translator_role(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    translator_names.append(n)
        if not translator_names:
            translator_names = _parse_names_from_raw(item.get("author") or "", want_translator=True)

        # 상품 HTML은 양쪽이 Step 3 에 진입할 경우를 대비해 한 번만 fetch
        product_html: Optional[str] = None

        author_bio = self.fetch_single_bio(item, writer_names, False, product_html)
        translator_bio = self.fetch_single_bio(item, translator_names, True, product_html)
        return author_bio, translator_bio

    # ── 원제 보완 ─────────────────────────────────────────────

    def enrich_original_title(self, item: Dict) -> Dict:
        """
        subInfo.originalTitle 이 비어 있으면 상품 상세 HTML 에서 원제를 보완.
        """
        sub = item.setdefault("subInfo", {})
        if (sub.get("originalTitle") or sub.get("subTitle") or "").strip():
            return item
        html = self.fetch_product_html(item)
        if not html:
            return item
        scraped = _scrape_original_title_from_html(html)
        if scraped:
            sub["originalTitle"] = scraped
        return item

    # ── 커리어 힌트 수집 ─────────────────────────────────────

    def collect_translator_career_hints(
        self,
        translator_names: List[str],
        item: Dict,
        use_category_filter: bool = True,
    ) -> Tuple[Dict[str, float], List[Dict]]:
        """
        역자명으로 ItemSearch 50권 → 카테고리 필터 → BioAnalyzer.career_hint_counts.
        ttbkey 없으면 빈 dict 반환.

        Returns
        -------
        (aggregated_career_hints, translators_info_for_llm)
        """
        if not self._ttbkey:
            return {}, []
        target_cat = item.get("categoryName") or item.get("categoryText") or ""
        aggregated: Dict[str, float] = {}
        translators_info: List[Dict] = []

        for name in translator_names[:3]:
            books = self.item_search_by_author(name, max_results=50)
            # 동명이인 방지: 역자 역할 확인
            filtered = [
                b for b in books
                if _is_translator_in_book(b, name)
                and (not use_category_filter or _category_overlap(target_cat, b.get("categoryName") or ""))
            ]
            if use_category_filter and not filtered:
                filtered = [b for b in books if _is_translator_in_book(b, name)]

            counts = BioAnalyzer.career_hint_counts(filtered)
            for k, v in counts.items():
                aggregated[k] = aggregated.get(k, 0.0) + v

            bio = self.collect_bio_from_api(item, name)
            if not bio.strip():
                aid = self._extract_id_from_api(item, name, True)
                if aid:
                    bio = self.scrape_bio_from_overview(aid)

            translators_info.append(BioAnalyzer.build_translator_info(
                name, bio, counts, len(filtered)
            ))
        return aggregated, translators_info


# ═══════════════════════════════════════════════════════════════
# 3. BioAnalyzer — Bio 텍스트 분석 순수 함수 모음
# ═══════════════════════════════════════════════════════════════

class BioAnalyzer:
    """Bio/커리어 텍스트 분석 정적 메서드 모음."""

    @staticmethod
    def script_weights(text: str) -> Dict[str, float]:
        """텍스트 내 문자 체계(가나/한자/라틴) 가중치 계산."""
        w: Dict[str, float] = {}
        if not text:
            return w
        if _RE_KANA.search(text):
            w["원제_가나(일본어)"] = w.get("원제_가나(일본어)", 0.0) + 2.0
        if _RE_HAN.search(text):
            w["원제_한자(중국어)"] = w.get("원제_한자(중국어)", 0.0) + 1.0
            w["원제_한자(일본어)"] = w.get("원제_한자(일본어)", 0.0) + 1.0
        if _RE_LATIN.search(text):
            w["원제_라틴(영미·유럽권)"] = w.get("원제_라틴(영미·유럽권)", 0.0) + 1.5
        return w

    @staticmethod
    def infer_lang_from_major(major: Optional[str]) -> Optional[str]:
        """전공 텍스트 → 언어 이름 추론."""
        if not major:
            return None
        for pat, lang in _MAJOR_LANG_RULES:
            if re.search(pat, major.strip(), re.I):
                return lang
        return None

    @staticmethod
    def extract_univ_major(text: str) -> Optional[Dict[str, Optional[str]]]:
        """소개글에서 대학/전공 Regex 추출."""
        if not text or not text.strip():
            return None
        _DEPT_SUFFIX = r"(?:학과|전공|학부|어과|어문학과?|문학과|사학과|과)"
        m = re.search(
            r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*"
            r"([가-힣A-Za-z·\s]{2,20}" + _DEPT_SUFFIX + r")",
            text,
        )
        if not m:
            m = re.search(
                r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*에서\s*"
                r"([가-힣A-Za-z·\s]{2,20}" + _DEPT_SUFFIX + r")",
                text,
            )
        if not m:
            return None
        uni, maj = m.group(1).strip(), m.group(2).strip()
        return {
            "university": uni,
            "major": maj,
            "inferred_language": BioAnalyzer.infer_lang_from_major(maj),
        }

    @staticmethod
    def confidence_from_bio(bio: str, univ_major: Optional[Dict]) -> str:
        """Bio 풍부도에 따라 high/medium/low 반환."""
        if univ_major and univ_major.get("inferred_language"):
            return "high"
        if bio and len(bio.strip()) > 100:
            return "medium"
        return "low"

    @staticmethod
    def career_hint_counts(books: List[Dict]) -> Dict[str, float]:
        """번역작 목록에서 언어/원제 힌트 가중치 집계."""
        counts: Dict[str, float] = {}
        for b in books:
            sub = b.get("subInfo") or {}
            ot = (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
            title = (b.get("title") or "") + " " + (b.get("description") or "")
            src = ot if ot else title
            for k, v in BioAnalyzer.script_weights(src).items():
                counts[k] = counts.get(k, 0.0) + v
            if ot and _RE_LATIN.search(ot) and not re.search(r"[가-힣]", ot):
                counts["원제_라틴_보조(영어 가능)"] = counts.get("원제_라틴_보조(영어 가능)", 0.0) + 0.5
        return counts

    @staticmethod
    def collapse_career_hints(hints: Mapping[str, float]) -> Dict[str, float]:
        """커리어 힌트 레이블 → 언어 이름 단위로 합산."""
        collapsed: Dict[str, float] = defaultdict(float)
        for label, score in hints.items():
            if score <= 0:
                continue
            lang = _CAREER_HINT_LANG_MAP.get(label)
            if lang:
                weight = score * 0.6 if label.startswith("메타_") else score
                collapsed[lang] += weight
        return dict(collapsed)

    @staticmethod
    def best_career_lang(hints: Mapping[str, float]) -> Optional[str]:
        """커리어 힌트에서 가장 높은 언어 이름 반환."""
        collapsed = BioAnalyzer.collapse_career_hints(hints)
        if not collapsed:
            return None
        return max(collapsed, key=lambda k: collapsed[k])

    @staticmethod
    def build_author_info(name: str, bio: str) -> Dict[str, Any]:
        """LLM 입력용 저자 정보 묶음."""
        bio_s = (bio or "").strip()
        name_s = (name or "").strip()
        return {
            "name": name_s,
            "bio_excerpt": bio_s[:3000] if bio_s else None,
            "script_weights": BioAnalyzer.script_weights(f"{name_s} {bio_s[:2000]}"),
            "univ_major_regex": BioAnalyzer.extract_univ_major(bio_s) if bio_s else None,
        }

    @staticmethod
    def build_translator_info(
        name: str,
        bio: str,
        career_hint_counts: Mapping[str, float],
        filtered_book_count: int,
    ) -> Dict[str, Any]:
        """LLM 입력용 역자 정보 묶음."""
        bio_s = (bio or "").strip()
        return {
            "name": (name or "").strip(),
            "bio_excerpt": bio_s[:3000] if bio_s else None,
            "univ_major_regex": BioAnalyzer.extract_univ_major(bio_s) if bio_s else None,
            "career_hint_counts": dict(career_hint_counts),
            "filtered_translator_book_count": filtered_book_count,
        }

    @staticmethod
    def build_book_info(item: Dict) -> Dict[str, Any]:
        """LLM 입력용 도서 메타데이터 묶음."""
        sub = item.get("subInfo") or {}
        desc_parts: List[str] = []
        for key in ("fulldescription", "fullDescription", "Story", "story", "description"):
            v = item.get(key) or sub.get(key)
            if isinstance(v, str) and v.strip():
                desc_parts.append(v.strip())
        desc = "\n\n".join(dict.fromkeys(desc_parts))[:8000]
        ot = (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
        title = (item.get("title") or "").strip()
        return {
            "title": title or None,
            "original_title": ot or None,
            "categoryName": item.get("categoryName") or item.get("categoryText"),
            "publisher": item.get("publisher"),
            "description": desc or None,
            "script_weights": BioAnalyzer.script_weights(ot or title),
        }


# ═══════════════════════════════════════════════════════════════
# 4. 모듈 레벨 순수 함수 (역할 판별, 파싱 등)
# ═══════════════════════════════════════════════════════════════

def _is_translator_role(role: str) -> bool:
    r = (role or "").strip()
    if not r:
        return False
    if any(m in r for m in _TRANSLATOR_ROLE_KEYS):
        return True
    if "역" in r and not any(x in r for x in ("지은이", "지음", "감수", "교정", "편집")):
        return True
    return False


def _is_writer_role(role: str) -> bool:
    r = (role or "").strip()
    return any(k in r for k in _WRITER_ROLE_KEYS)


def _parse_names_from_raw(raw_author: str, want_translator: bool) -> List[str]:
    """subInfo.authors 없을 때 item['author'] 원시 문자열에서 이름 파싱."""
    names: List[str] = []
    tr_kw = ("옮긴이", "역자", "옮김", "역")
    wr_kw = ("지은이", "지음", "글")
    for part in (raw_author or "").split(","):
        if want_translator:
            if not any(k in part for k in tr_kw):
                continue
            name = re.sub(r"\(.*?\)|옮긴이|역자|옮김|지은이|지음|역", "", part, flags=re.I).strip()
        else:
            if not any(k in part for k in wr_kw):
                continue
            if any(k in part for k in tr_kw):
                continue
            name = re.sub(r"\(.*?\)|지은이|지음|글|옮긴이|역자|옮김", "", part, flags=re.I).strip()
        if name:
            names.append(name)
    return list(dict.fromkeys(names))


def _is_translator_in_book(book: Dict, target_name: str) -> bool:
    """커리어 필터용: 책에서 target_name 이 역자인지 확인."""
    sub = book.get("subInfo") or {}
    authors = sub.get("authors")
    if isinstance(authors, list) and authors:
        for auth in authors:
            if not isinstance(auth, dict):
                continue
            if (auth.get("authorName") or "").strip() != target_name.strip():
                continue
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if any(m in role for m in ("옮긴이", "역자", "역", "옮김")):
                return True
        return False
    raw = book.get("author") or ""
    esc = re.escape(target_name.strip())
    return bool(re.search(rf"{esc}\s*\([^)]*(?:옮긴이|역자|옮김|역)[^)]*\)", raw))


def _category_overlap(target_cat: str, book_cat: str) -> bool:
    """대분류 첫 세그먼트만 비교해 겹치면 True."""
    def _segs(cat: str) -> List[str]:
        s = cat.replace("국내도서", "").replace("외국도서", "").replace("eBook", "")
        return [p.strip() for p in s.split(">") if p.strip()]
    ta, ba = _segs(target_cat), _segs(book_cat)
    if not ta or not ba:
        return True
    return ta[0] == ba[0]


def _extract_code_and_reason(content: str, code_key: str = "$h") -> Tuple[str, str, str]:
    """GPT 텍스트 응답 파싱 → (code, reason, signals)."""
    code = reason = signals = ""
    for ln in [l.strip() for l in (content or "").splitlines() if l.strip()]:
        if ln.startswith(f"{code_key}="):
            code = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#reason="):
            reason = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#signals="):
            signals = ln.split("=", 1)[1].strip()
    return code or "und", reason, signals


def _scrape_original_title_from_html(html: str) -> Optional[str]:
    """wproduct HTML 에서 원제 추출."""
    if not _SCRAPER_AVAILABLE or not (html or "").strip():
        return None
    soup = BeautifulSoup(html, "html.parser")

    def _clean(text: str) -> Optional[str]:
        t = re.sub(r"\s+", " ", (text or "").strip())
        if len(t) < 2 or t in _ORIGINAL_TITLE_LABELS:
            return None
        if re.search(r"^(HOME|로그인|장바구니|국내도서|외국도서|통합검색)", t):
            return None
        return t

    info = soup.find(class_=re.compile(r"p_goodstit_info", re.I))
    if info:
        h1 = info.find("h1")
        h1_text = h1.get_text(strip=True) if h1 else ""
        for tag in info.find_all(["span", "h2", "h3", "em", "a"]):
            if h1 and tag in h1.descendants:
                continue
            cand = _clean(tag.get_text(separator=" ", strip=True))
            if cand and cand != h1_text and not re.search(r"(지음|옮김|역자|출판)$", cand):
                return cand

    for lab in soup.find_all(["span", "dt", "th", "label", "b", "strong"]):
        if lab.get_text(strip=True) not in _ORIGINAL_TITLE_LABELS:
            continue
        for nxt in (lab.find_next_sibling(), lab.find_next(["dd", "span", "td", "div", "a"])):
            if nxt is None:
                continue
            cand = _clean(nxt.get_text(separator=" ", strip=True))
            if cand:
                return cand

    for cls_pat in (r"Ere_subTitle", r"subTitle", r"original", r"ori_title"):
        el = soup.find(class_=re.compile(cls_pat, re.I))
        if el:
            cand = _clean(el.get_text(separator=" ", strip=True))
            if cand:
                return cand
    return None


# ═══════════════════════════════════════════════════════════════
# 5. LangFieldBuilder — 메인 파이프라인 오케스트레이터
# ═══════════════════════════════════════════════════════════════

class LangFieldBuilder:
    """
    KORMARC 041/546 필드 생성 전담 클래스.

    Parameters
    ----------
    openai_client
        OpenAI() 인스턴스. None 이면 GPT 호출 스킵.
    ttbkey
        알라딘 TTB 키. SafeTrack(역자 커리어 검색) 에 사용.
    model
        GPT 모델명. 기본 'gpt-4o'.
    dbg_fn / dbg_err_fn
        로그 출력 함수. 기본 print.
    """

    # ── 카테고리 키워드 설정 ────────────────────────────────────

    LIT_KEYWORDS: Dict[str, List[str]] = {
        "ko": ["문학", "소설", "시", "희곡"],
        "en": ["literature", "fiction", "novel", "poetry", "poem", "drama", "play"],
    }
    NONFICTION_KEYWORDS: Dict[str, List[str]] = {
        "ko": ["역사", "근현대사", "서양사", "유럽사", "전기", "평전",
               "사회", "정치", "철학", "경제", "경영", "인문", "에세이", "수필"],
        "en": ["history", "biography", "memoir", "politics", "philosophy",
               "economics", "science", "technology", "nonfiction", "essay", "essays"],
    }
    SF_GUARD_KEYWORDS: Dict[str, List[str]] = {
        "ko": ["과학", "기술"],
        "en": ["science", "technology"],
    }
    CATEGORY_LANG_MAP: List[Tuple[List[str], str]] = [
        (["일본"],                     "jpn"),
        (["중국"],                     "chi"),
        (["영미", "영어", "아일랜드"], "eng"),
        (["프랑스"],                   "fre"),
        (["독일", "오스트리아"],       "ger"),
        (["러시아"],                   "rus"),
        (["이탈리아"],                 "ita"),
        (["스페인"],                   "spa"),
        (["포르투갈"],                 "por"),
        (["튀르키예", "터키"],         "tur"),
    ]
    CHAR_LANG_MAP: List[Tuple[str, str]] = [
        ("éèêàçùôâîû", "fre"),
        ("ñáíóú",       "spa"),
        ("ãõ",          "por"),
    ]

    def __init__(
        self,
        openai_client=None,
        ttbkey: str = "",
        model: str = "gpt-4o",
        dbg_fn: Optional[Callable] = None,
        dbg_err_fn: Optional[Callable] = None,
    ):
        self._client  = openai_client
        self._model   = model
        self._dbg     = dbg_fn     or (lambda *a: print("[DBG]", *a))
        self._dbg_err = dbg_err_fn or (lambda *a: print("[ERR]", *a))
        self._tools   = AladinTools(ttbkey=ttbkey)

    # ─────────────────────────────────────────────────────────
    # 단계 1: $a 본문 언어 판정
    # ─────────────────────────────────────────────────────────

    def _step1_lang_a(self, title: str, category_text: str, publisher: str) -> str:
        """
        규칙 → 국내도서 가드 → GPT 보완(und/eng 시).
        """
        lang_a = self.detect_language(title)
        self._dbg(f"📘 [Step1] 규칙 1차 lang_a={lang_a}")

        if self.is_domestic_category(category_text):
            self._dbg("📘 [Step1] '국내도서' → $a=kor 강제")
            return "kor"

        if lang_a in ("und", "eng"):
            self._dbg("📘 [Step1] und/eng → GPT $a 재판정")
            gpt_a = self._gpt_main_lang(title, category_text, publisher)
            lang_a = gpt_a if gpt_a in ALLOWED_CODES else "und"

        return lang_a

    def _gpt_main_lang(self, title: str, category: str, publisher: str) -> str:
        """$a 본문 언어 GPT 판정."""
        if not self._client:
            return "und"
        prompt = (
            f"아래 도서의 본문 언어(041 $a)를 ISDS 코드로 추정.\n"
            f"가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur\n\n"
            f"입력:\n- 제목: {title}\n- 분류: {category}\n- 출판사: {publisher}\n\n"
            "지침:\n"
            "- '본문 언어'는 현시본(Manifestation) 언어.\n"
            "- 카테고리에 '국내도서'가 있거나 제목에 한글이 1자라도 있으면 반드시 kor.\n"
            "- 저자 국적·원작 언어 단서 사용 금지.\n"
            "- 불확실하면 'und'.\n\n"
            "출력형식:\n$a=[ISDS 코드]\n#reason=[근거 요약]"
        )
        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": "사서용 본문 언어 추정기"},
                    {"role": "user",   "content": prompt},
                ],
                temperature=0,
            )
            content = (resp.choices[0].message.content or "").strip()
            code, reason, _ = _extract_code_and_reason(content, "$a")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"🧭 [GPT $a] {code}  ← {reason}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류 ($a): {e}")
            return "und"

    # ─────────────────────────────────────────────────────────
    # 단계 2: 카테고리 분류 (문학 vs 비문학)
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def tokenize_category(text: str) -> List[str]:
        if not text:
            return []
        t = re.sub(r"[()]+", " ", text)
        raw = re.split(r"[>/\s]+", t)
        tokens: List[str] = []
        for w in raw:
            w = w.strip()
            if not w:
                continue
            if "/" in w and w.count("/") <= 3 and len(w) <= 20:
                tokens.extend(p for p in w.split("/") if p)
            else:
                tokens.append(w)
        lower_tokens = tokens + [
            w.lower() for w in tokens
            if any("A" <= ch <= "Z" or "a" <= ch <= "z" for ch in w)
        ]
        return lower_tokens

    @staticmethod
    def _has_kw(tokens: List[str], kws: List[str]) -> bool:
        s = set(tokens)
        return any(k in s for k in kws)

    @staticmethod
    def _trigger_kw(tokens: List[str], kws: List[str]) -> Optional[str]:
        s = set(tokens)
        for k in kws:
            if k in s:
                return k
        return None

    def is_literature_category(self, category_text: str) -> bool:
        tokens = self.tokenize_category(category_text or "")
        return (
            self._has_kw(tokens, self.LIT_KEYWORDS["ko"])
            or self._has_kw(tokens, self.LIT_KEYWORDS["en"])
        )

    @staticmethod
    def is_literature_top(category_text: str) -> bool:
        return "소설/시/희곡" in (category_text or "")

    def is_nonfiction_override(self, category_text: str) -> bool:
        """
        비문학 키워드 → True.
        단, 소설/시/희곡 최상위면 SF_GUARD(과학/기술)는 제외.
        """
        tokens  = self.tokenize_category(category_text or "")
        lit_top = self.is_literature_top(category_text or "")
        k = (
            self._trigger_kw(tokens, self.NONFICTION_KEYWORDS["ko"])
            or self._trigger_kw(tokens, self.NONFICTION_KEYWORDS["en"])
        )
        if k:
            self._dbg(f"🔎 [Step2] 비문학 키워드: '{k}'")
            return True
        if not lit_top:
            k2 = (
                self._trigger_kw(tokens, self.SF_GUARD_KEYWORDS["ko"])
                or self._trigger_kw(tokens, self.SF_GUARD_KEYWORDS["en"])
            )
            if k2:
                self._dbg(f"🔎 [Step2] 비문학(과학/기술) 키워드: '{k2}'")
                return True
        if lit_top:
            self._dbg("🔎 [Step2] 문학 최상위 → SF 보호 유지")
        return False

    @staticmethod
    def is_domestic_category(category_text: str) -> bool:
        return "국내도서" in (category_text or "")

    # ─────────────────────────────────────────────────────────
    # 단계 3A: 문학 파이프라인
    # ─────────────────────────────────────────────────────────

    def _step3a_literature(
        self,
        title: str,
        original_title: str,
        category_text: str,
        publisher: str,
        author: str,
        subject_lang: str,
    ) -> Tuple[Optional[str], Optional[str]]:
        """
        문학: Rule → GPT-General → GPT-Author
        Returns (lang_h, author_hint)
        """
        self._dbg("📘 [Step3A] 문학 파이프라인: Rule → GPT-General → GPT-Author")
        rule_h = self.detect_language(original_title) if original_title else "und"

        # Rule
        result = subject_lang or rule_h or None
        if result and result != "und":
            self._dbg(f"📘 [Step3A/Rule] 확정: {result}")
            return result, None

        # GPT-General
        code = self._gpt_general_lang(title, category_text, publisher, author, original_title)
        if code and code in ALLOWED_CODES:
            self._dbg(f"📘 [Step3A/GPT-General] 확정: {code}")
            return code, None

        # GPT-Author
        author_hint = self._gpt_author_lang(author, title, category_text, publisher)
        return None, author_hint

    # ─────────────────────────────────────────────────────────
    # 단계 3B: 비문학 파이프라인 (하이브리드)
    # ─────────────────────────────────────────────────────────

    def _step3b_nonfiction(
        self,
        item: Dict,
        title: str,
        original_title: str,
        category_text: str,
        publisher: str,
        author: str,
        subject_lang: str,
    ) -> Tuple[Optional[str], Optional[str]]:
        """
        비문학 하이브리드 파이프라인:
          (사전) Bio 수집
          FastTrack: 전공/문자체계 단서 분석 → confidence 평가
          [GPT 있으면] 하이브리드 단일 호출
          [SafeTrack: confidence=low] 역자 커리어 수집 → GPT 재호출
          Rule 폴백
        Returns (lang_h, author_hint)
        """
        self._dbg("📘 [Step3B] 비문학 파이프라인 시작")
        rule_h = self.detect_language(original_title) if original_title else "und"

        # ── 사전 작업: Bio 수집 ───────────────────────────────
        self._dbg("📘 [Step3B/Bio] API-First Bio 수집 시작…")
        try:
            author_bio, translator_bio = self._tools.fetch_bios(item)
            if author_bio:
                self._dbg(f"📘 [Step3B/Bio] 저자 Bio {len(author_bio)}자")
            if translator_bio:
                self._dbg(f"📘 [Step3B/Bio] 역자 Bio {len(translator_bio)}자")
            if not author_bio and not translator_bio:
                self._dbg("📘 [Step3B/Bio] Bio 없음")
        except Exception as e:
            self._dbg_err(f"Bio 수집 오류: {e}")
            author_bio = translator_bio = ""

        # ── FastTrack: 저자 단서 분석 ─────────────────────────
        author_univ  = BioAnalyzer.extract_univ_major(author_bio)
        author_sw    = BioAnalyzer.script_weights(f"{author} {original_title} {author_bio[:500]}")
        trans_univ   = BioAnalyzer.extract_univ_major(translator_bio)
        author_conf  = BioAnalyzer.confidence_from_bio(author_bio, author_univ)
        self._dbg(f"📘 [FastTrack] 저자 단서 confidence={author_conf}")
        if author_univ:
            self._dbg(f"📘 [FastTrack] 저자 전공: {author_univ}")
        if trans_univ:
            self._dbg(f"📘 [FastTrack] 역자 전공: {trans_univ}")

        # ── 역자 이름 목록 ────────────────────────────────────
        sub = item.get("subInfo") or {}
        translator_names: List[str] = []
        for auth in (sub.get("authors") or []):
            if not isinstance(auth, dict):
                continue
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _is_translator_role(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    translator_names.append(n)
        if not translator_names:
            translator_names = _parse_names_from_raw(item.get("author") or "", want_translator=True)

        # ── SafeTrack (confidence=low 시만 실행) ─────────────
        aggregated_career: Dict[str, float] = {}
        translators_info_llm: List[Dict] = [
            BioAnalyzer.build_translator_info(
                n, translator_bio, {}, 0
            ) for n in translator_names[:2]
        ]

        if author_conf == "low" and self._tools._ttbkey:
            self._dbg("📘 [SafeTrack] confidence=low → 역자 커리어 수집")
            try:
                aggregated_career, translators_info_llm = (
                    self._tools.collect_translator_career_hints(
                        translator_names, item, use_category_filter=True
                    )
                )
                if aggregated_career:
                    best = BioAnalyzer.best_career_lang(aggregated_career)
                    self._dbg(f"📘 [SafeTrack] 커리어 최고 언어: {best}")
            except Exception as e:
                self._dbg_err(f"SafeTrack 오류: {e}")

        # ── GPT 하이브리드 단일 호출 ──────────────────────────
        if self._client:
            authors_info_llm = [BioAnalyzer.build_author_info(author, author_bio)]
            book_info_llm    = BioAnalyzer.build_book_info(item)
            llm_result = self._gpt_hybrid_nonfiction(
                authors_info_llm, book_info_llm, translators_info_llm
            )
            if llm_result:
                lang_name = llm_result.get("inferred_language", "")
                self._dbg(
                    f"📘 [Step3B/LLM] inferred_language={lang_name} "
                    f"confidence={llm_result.get('author_signal_confidence')} "
                    f"indirect={llm_result.get('is_indirect_translation')}"
                )
                isds = _LANG_NAME_TO_ISDS.get(lang_name)
                if isds and isds in ALLOWED_CODES:
                    self._dbg(f"📘 [Step3B/LLM] 확정: {isds}")
                    return isds, None

        # ── Rule 폴백 ─────────────────────────────────────────
        result = subject_lang or rule_h or None
        if result and result != "und":
            self._dbg(f"📘 [Step3B/Rule] 폴백 확정: {result}")
            return result, None

        # ── 커리어 힌트 폴백 (GPT 없을 때) ──────────────────
        if aggregated_career:
            best = BioAnalyzer.best_career_lang(aggregated_career)
            isds = _LANG_NAME_TO_ISDS.get(best or "")
            if isds and isds in ALLOWED_CODES:
                self._dbg(f"📘 [Step3B/Career] 폴백 확정: {isds}")
                return isds, None

        return None, None

    # ─────────────────────────────────────────────────────────
    # GPT 보조 메서드
    # ─────────────────────────────────────────────────────────

    def _gpt_general_lang(
        self,
        title: str,
        category: str,
        publisher: str,
        author: str,
        original_title: str,
        author_bio: str = "",
        translator_bio: str = "",
    ) -> str:
        """GPT 일반 원서 언어 판정 (문학 분기용)."""
        if not self._client:
            return "und"
        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"
        prompt = (
            f"아래 도서의 원서 언어(041 $h)를 ISDS 코드로 추정.\n"
            f"가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur\n\n"
            f"도서정보:\n- 제목: {title}\n- 원제: {original_title or '(없음)'}\n"
            f"- 분류: {category}\n- 출판사: {publisher}\n- 저자: {author}{bio_block}\n\n"
            "지침:\n"
            "- 국가/지역을 언어로 직접 치환하지 말 것.\n"
            "- 저자 국적·집필 언어·최초 출간 언어 우선.\n"
            "- 불확실하면 'und'.\n\n"
            "출력형식:\n$h=[ISDS 코드]\n#reason=[근거 요약]"
        )
        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": "사서용 언어 추정기"},
                    {"role": "user",   "content": prompt},
                ],
                temperature=0,
            )
            content = (resp.choices[0].message.content or "").strip()
            code, reason, _ = _extract_code_and_reason(content, "$h")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"🧭 [GPT General $h] {code}  ← {reason}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류 (general): {e}")
            return "und"

    def _gpt_author_lang(
        self,
        author: str,
        title: str,
        category: str,
        publisher: str,
        author_bio: str = "",
        translator_bio: str = "",
    ) -> str:
        """GPT 저자 기반 원서 언어 판정 (문학 최종 후보)."""
        if not self._client or not author:
            return "und"
        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"
        prompt = (
            f"저자 정보를 중심으로 원서 언어(041 $h)를 ISDS 코드로 추정.\n"
            f"가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur\n\n"
            f"입력:\n- 저자: {author}\n- 제목: {title}\n"
            f"- 분류: {category}\n- 출판사: {publisher}{bio_block}\n\n"
            "지침:\n- 저자 국적·집필 언어·대표 작품 원어 우선.\n"
            "- 국가=언어 단순 치환 금지.\n- 불확실하면 'und'.\n\n"
            "출력형식:\n$h=[ISDS 코드]\n#reason=[근거 요약]"
        )
        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": "저자 기반 원서 언어 추정기"},
                    {"role": "user",   "content": prompt},
                ],
                temperature=0,
            )
            content = (resp.choices[0].message.content or "").strip()
            code, reason, _ = _extract_code_and_reason(content, "$h")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"🧭 [GPT Author $h] {code}  ← {reason}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류 (author): {e}")
            return "und"

    def _gpt_hybrid_nonfiction(
        self,
        authors_info: List[Dict],
        book_info: Dict,
        translators_info: List[Dict],
    ) -> Optional[Dict[str, Any]]:
        """
        비문학 하이브리드 단일 GPT 호출.
        저자·도서 우선, 번역가 폴백, 고유명사 규칙(A~E) 포함.
        JSON 응답 → dict 반환. 실패 시 None.
        """
        if not self._client:
            return None

        # ── 시스템 프롬프트 (trans.py 규칙 A~E 통합) ──────────
        system = (
            "당신은 **한국어로 번역·출간된 외국 도서**의 **원서 언어·원서 국가**만 추론하는 전문가입니다.\n"
            "입력은 알라딘 **번역서** 데이터입니다. 한국어 제목·'국내도서' 분류는 **번역본 유통 정보**일 뿐, "
            "원서가 한국어라는 증거가 **절대 아닙니다**.\n"
            "아래 [최우선 금지·강제 규칙]을 최우선 적용하세요. 예외 없음.\n\n"
            "══════════════════════════════════════════════════════\n"
            "## [최우선] 절대 금지·강제 규칙\n"
            "══════════════════════════════════════════════════════\n\n"
            "### 규칙 A. '국내도서' ≠ 한국어 원서\n"
            "book.categoryName에 '국내도서', '국내', '한국' 등이 있어도 그것은 "
            "**한국 출판사가 번역·출간한 책**이라는 알라딘 **유통 분류**일 뿐입니다.\n"
            "**절대 금지:** '국내도서'만 보고 inferred_language='한국어' 또는 inferred_country='한국' 판정.\n\n"
            "### 규칙 B. 외국인 이름 음차 — bio 부재여도 한국어 원서로 보지 말 것\n"
            "authors[].bio_excerpt가 null·공백이어도 authors[].name이 **외국 인명의 한글 음차**이면 "
            "한국인·한국어 원서 판정 **절대 금지**.\n"
            "  · 예: 아나스타샤 메이블, 톰 스미스, 레오 톨스토이, 조지 오웰 등\n"
            "  · 전형적 한국 성씨(김·이·박·최·정·강·조·윤·장·임)만 있는 이름이 아니면 외국인 저자로 간주.\n\n"
            "### 규칙 D. 도서 제목의 결정적 고유명사 최우선 적용\n"
            "저자 정보가 부실해도 book.title·book.description에 **특정 국가·문화권을 명확히 지시하는 고유명사**가 있으면 "
            "번역가 폴백 전에 **즉시** 해당 본고장을 원서 국가·언어로 판정.\n"
            "  · 일본: 지브리, 라퓨타, 토토로, 모노노케, 미야자키 등 → 일본어/일본\n"
            "  · 미국: 마블, 디즈니, 픽사, 스타워즈, 해리포터(영미판) 등 → 영어/미국\n"
            "  · 영국: 셜록, 007, 롤링 등 → 영어/영국\n\n"
            "### 규칙 C. 저자 단서 부실 시 번역가 폴백 **즉시·적극** 가동 (규칙 D 적용 후)\n"
            "author_signal_confidence=low이고 규칙 D 미해당 시:\n"
            "  · translators[].univ_major_regex.inferred_language 적극 수용\n"
            "  · translators[].career_hint_counts 누적이 큰 축 채택\n"
            "  · **단, 규칙 D의 일본 IP가 title에 있으면 영문과 역자여도 미국 판정 금지**\n\n"
            "### 규칙 E. 한국계·해외파 저자\n"
            "저자 이름이 한국식이어도 bio_excerpt에서 Stanford·Harvard·Forbes·NYU 등 영미권 기관·언론이 "
            "주축이면 inferred_language=영어·inferred_country=미국 등으로 판정.\n\n"
            "══════════════════════════════════════════════════════\n"
            "## 추론 우선순위\n"
            "══════════════════════════════════════════════════════\n"
            "1순위: 저자(name, bio_excerpt, script_weights, univ_major_regex)\n"
            "2순위: 도서 메타(title, description, original_title) — 규칙 D 고유명사 포함\n"
            "3순위: 번역가(univ_major_regex, career_hint_counts) — 규칙 C 조건에서만\n\n"
            "## author_signal_confidence\n"
            "- high: bio에 해외 대학·활동·언론 결정적 맥락, 또는 규칙 D 고유명사로 확정\n"
            "- medium: bio 일부 단서 있음\n"
            "- low: bio 없음/무의미 + 외국인 음차 → 규칙 D 먼저, 미해당 시 규칙 C\n\n"
            "## reasoning_process (한국어, 순서 고정)\n"
            "① 분석 맥락 → ② 저자(name·bio) → ③ 규칙 D(title 고유명사) → "
            "④ 국내도서/가짜 원제 배제 → ⑤ 규칙 C 번역가 폴백 여부 → ⑥ 최종 결론\n\n"
            "반드시 JSON 객체 하나만 반환. 키:\n"
            '- reasoning_process (string)\n'
            '- author_signal_confidence ("high"|"medium"|"low")\n'
            '- inferred_language (string, 한국어 표기: 영어·일본어·러시아어 등)\n'
            '- inferred_country (string, 한국어 표기: 미국·일본·러시아 등)\n'
            '- is_indirect_translation (boolean)\n'
        )

        payload = {
            "authors":     authors_info,
            "book":        book_info,
            "translators": translators_info,
        }
        body = {
            "model":    self._model,
            "messages": [
                {"role": "system", "content": system},
                {"role": "user",   "content": json.dumps(payload, ensure_ascii=False, indent=2)},
            ],
            "response_format": {"type": "json_object"},
        }
        try:
            resp = self._client.chat.completions.create(**{
                k: v for k, v in body.items() if k != "model"
            }, model=self._model)
            raw = (resp.choices[0].message.content or "").strip()
            obj = json.loads(raw)
            conf = (obj.get("author_signal_confidence") or "low").strip().lower()
            if conf not in ("high", "medium", "low"):
                conf = "low"
            return {
                "reasoning_process":       (obj.get("reasoning_process") or "").strip(),
                "author_signal_confidence": conf,
                "inferred_language":       (obj.get("inferred_language") or "").strip() or "판별 불가",
                "inferred_country":        (obj.get("inferred_country") or "").strip() or "판별 불가",
                "is_indirect_translation": bool(obj.get("is_indirect_translation")),
                "source": "llm",
            }
        except Exception as e:
            self._dbg_err(f"GPT 오류 (hybrid): {e}")
            return None

    # ─────────────────────────────────────────────────────────
    # 단계 4: 충돌 조정
    # ─────────────────────────────────────────────────────────

    def reconcile_language(
        self,
        candidate: str,
        fallback_hint: Optional[str] = None,
        author_hint: Optional[str] = None,
    ) -> str:
        if author_hint and author_hint != "und" and author_hint != candidate:
            self._dbg(f"🔁 [조정] author_hint({author_hint}) ≠ 후보({candidate}) → author_hint 우선")
            return author_hint
        if fallback_hint and fallback_hint != "und" and fallback_hint != candidate:
            if candidate in {"ita", "fre", "spa", "por"} and fallback_hint == "eng":
                return candidate  # 영어 힌트 과대검출 방지
            self._dbg(f"🔁 [조정] fallback({fallback_hint}) → 우선")
            return fallback_hint
        return candidate

    # ─────────────────────────────────────────────────────────
    # 규칙 기반 언어 감지 유틸
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def detect_language_by_unicode(text: str) -> str:
        text = re.sub(r"[\s\W_]+", "", text or "")
        if not text:
            return "und"
        c = text[0]
        if "\uac00" <= c <= "\ud7a3": return "kor"
        if "\u3040" <= c <= "\u30ff": return "jpn"
        if "\u4e00" <= c <= "\u9fff": return "chi"
        if "\u0600" <= c <= "\u06FF": return "ara"
        return "und"

    @staticmethod
    def override_language_by_keywords(text: str, initial_lang: str) -> str:
        text = (text or "").lower()
        if initial_lang == "chi" and re.search(r"[\u3040-\u30ff]", text):
            return "jpn"
        if initial_lang in ("und", "eng"):
            if "spanish"    in text or "español"    in text: return "spa"
            if "italian"    in text or "italiano"   in text: return "ita"
            if "french"     in text or "français"   in text: return "fre"
            if "portuguese" in text or "português"  in text: return "por"
            if "german"     in text or "deutsch"    in text: return "ger"
            for chars, lang in LangFieldBuilder.CHAR_LANG_MAP:
                if any(ch in text for ch in chars):
                    return lang
        return initial_lang

    def detect_language(self, text: str) -> str:
        lang = self.detect_language_by_unicode(text)
        return self.override_language_by_keywords(text, lang)

    @staticmethod
    def detect_language_from_category(text: str) -> Optional[str]:
        words = re.split(r"[>/\s]+", text or "")
        for w in words:
            for keywords, lang in LangFieldBuilder.CATEGORY_LANG_MAP:
                if any(kw in w for kw in keywords):
                    return lang
        return None

    # ─────────────────────────────────────────────────────────
    # 메인 진입점: get_kormarc_tags
    # ─────────────────────────────────────────────────────────

    def get_kormarc_tags(
        self,
        item: Dict,
        detail: Dict,
    ) -> Tuple[Optional[str], Optional[str], str]:
        """
        알라딘 API item dict + 크롤링 detail dict →
        (tag_041, tag_546, original_title).

        번역서가 아닐 때  : (None, None, original_title)
        번역서일 때        : ("041 $akor $heng", "영어 원작을 한국어로 번역", original_title)
        예외 발생 시       : ("📕 예외: …", "", original_title)
        """
        item   = item   or {}
        detail = detail or {}

        title     = item.get("title",     "") or ""
        publisher = item.get("publisher", "") or ""
        author    = item.get("author",    "") or ""

        subinfo        = (item.get("subInfo") or {}) or {}
        original_title = _html_stdlib.unescape(subinfo.get("originalTitle", "") or "")
        if not original_title:
            original_title = detail.get("original_title", "") or ""

        subject_lang  = detail.get("subject_lang") or ""
        category_text = (
            item.get("categoryText", "") or item.get("categoryName", "")
            or detail.get("category_text", "") or ""
        )

        try:
            # ── 원제 없으면 웹에서 보완 ─────────────────────────
            if not original_title:
                item = self._tools.enrich_original_title(item)
                original_title = _html_stdlib.unescape(
                    (item.get("subInfo") or {}).get("originalTitle", "") or ""
                )

            # ── 단계 1: $a 본문 언어 ────────────────────────────
            lang_a = self._step1_lang_a(title, category_text, publisher)
            self._dbg(f"📘 [결과] lang_a={lang_a}")

            # ── 단계 2: 카테고리 분류 ───────────────────────────
            lit_raw     = self.is_literature_category(category_text)
            nf_override = self.is_nonfiction_override(category_text)
            is_lit      = lit_raw and not nf_override

            if lit_raw and not nf_override:
                self._dbg("📘 [Step2] 문학으로 판정")
            elif lit_raw and nf_override:
                self._dbg("📘 [Step2] 겉보기 문학 + 비문학 요소 → 비문학")
            elif not lit_raw and nf_override:
                self._dbg("📘 [Step2] 비문학으로 판정")
            else:
                self._dbg("📘 [Step2] 분류 약함 → 비문학 경로")
                is_lit = False  # 단서 약하면 비문학(더 정밀한 분석) 선택

            rule_h = self.detect_language(original_title) if original_title else "und"
            fallback_hint = subject_lang or rule_h or None

            # ── 단계 3: $h 원서 언어 ────────────────────────────
            if is_lit:
                lang_h, author_hint = self._step3a_literature(
                    title, original_title, category_text, publisher, author, subject_lang
                )
            else:
                lang_h, author_hint = self._step3b_nonfiction(
                    item, title, original_title, category_text, publisher, author, subject_lang
                )

            # ── 단계 4: 충돌 조정 ───────────────────────────────
            lang_h = self.reconcile_language(
                candidate=lang_h or "und",
                fallback_hint=fallback_hint,
                author_hint=author_hint,
            )
            lang_h = lang_h if lang_h in ALLOWED_CODES else "und"
            self._dbg(f"📘 [결과] lang_h={lang_h}")

            # ── 태그 조합 ────────────────────────────────────────
            if lang_h and lang_h != lang_a and lang_h != "und":
                tag_041 = f"041 $a{lang_a} $h{lang_h}"
            else:
                tag_041 = f"041 $a{lang_a}"

            if "$h" not in tag_041:
                return None, None, original_title

            tag_546 = self.generate_546_from_041(tag_041)
            return tag_041, tag_546, original_title

        except Exception as e:
            self._dbg_err(f"get_kormarc_tags 예외: {e}")
            return f"📕 예외 발생: {e}", "", original_title

    # ─────────────────────────────────────────────────────────
    # 546 텍스트 생성
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def generate_546_from_041(marc_041: str) -> str:
        """'041 $akor $hrus' → '러시아어 원작을 한국어로 번역'"""
        a_codes: List[str] = []
        h_code: Optional[str] = None
        for part in marc_041.split():
            if part.startswith("$a"):
                a_codes.append(part[2:])
            elif part.startswith("$h"):
                h_code = part[2:]
        if len(a_codes) == 1:
            a_lang = ISDS_LANGUAGE_CODES.get(a_codes[0], "알 수 없음")
            if h_code:
                h_lang = ISDS_LANGUAGE_CODES.get(h_code, "알 수 없음")
                return f"{h_lang} 원작을 {a_lang}로 번역"
            return f"{a_lang}로 씀"
        if len(a_codes) > 1:
            langs = [ISDS_LANGUAGE_CODES.get(c, "알 수 없음") for c in a_codes]
            return f"{'、'.join(langs)} 병기"
        return "언어 정보 없음"

    # ─────────────────────────────────────────────────────────
    # MRK 포맷 변환
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def as_mrk_041(tag_041: Optional[str]) -> Optional[str]:
        """'041 $akor $hrus' → '=041  1\\$akor$hrus'"""
        if not tag_041:
            return None
        s = re.sub(r"^=?\s*041\s*", "", tag_041.strip())
        s = re.sub(r"\s+", "", s)
        if not s.startswith("$a"):
            return None
        return f"=041  1\\{s}"

    @staticmethod
    def as_mrk_546(tag_546_text: Optional[str]) -> Optional[str]:
        """'러시아어 원작을 한국어로 번역' → '=546  \\\\$a러시아어 원작을 한국어로 번역'"""
        if not tag_546_text:
            return None
        t = tag_546_text.strip()
        if not t:
            return None
        if t.startswith("=546"):
            return t
        if t.startswith("$a"):
            return f"=546  \\\\{t}"
        return f"=546  \\\\$a{t}"

    # ─────────────────────────────────────────────────────────
    # 헬퍼 (하위 호환)
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def extract_lang_h(tag_041_text: Optional[str]) -> Optional[str]:
        if not tag_041_text:
            return None
        m = re.search(r"\$h([a-z]{3})", tag_041_text, re.IGNORECASE)
        return m.group(1).lower() if m else None

    @staticmethod
    def lang3_from_tag041(tag_041: Optional[str]) -> Optional[str]:
        if not tag_041:
            return None
        m = re.search(r"\$a([a-z]{3})", tag_041, flags=re.I)
        return m.group(1).lower() if m else None


# ═══════════════════════════════════════════════════════════════
# 6. 모듈 레벨 하위 호환 래퍼
# ═══════════════════════════════════════════════════════════════

def generate_546_from_041_kormarc(marc_041: str) -> str:
    return LangFieldBuilder.generate_546_from_041(marc_041)
