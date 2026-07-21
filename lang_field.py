"""
lang_field.py
─────────────────────────────────────────────────────────────────────────────
KORMARC 041(언어코드) · 546(언어주기) 필드 생성 모듈

【포함 기능】
  - ISDS 언어코드 상수 / 허용코드 집합
  - GPT 기반 언어 판정   : gpt_guess_main_lang()
                           gpt_nonfiction_payload()
                           gpt_guess_from_original_title_only()
  - 규칙 기반 언어 감지  : detect_language_by_unicode()
                           override_language_by_keywords()
                           detect_language()
                           detect_language_from_category()
  - 카테고리 판정 유틸   : tokenize_category(), is_literature_category(),
                           is_nonfiction_override(), is_domestic_category()
  - $h 결정 로직         : determine_h_language()
                           _try_rule()
  - 충돌 조정            : reconcile_language()
  - 최종 KORMARC 태그    : get_kormarc_tags()          → (tag_041, tag_546, orig_title)
  - 546 텍스트 생성       : LangFieldBuilder.generate_546_from_041()
  - MRK 포맷 변환        : _as_mrk_041(), _as_mrk_546()
  - 헬퍼                 : _extract_lang_h_from_041(), _lang3_from_tag041()

【외부 의존】
  - openai.OpenAI 클라이언트 (client)   : 호출부에서 주입
  - dbg / dbg_err 로거                  : 호출부에서 주입 (없으면 print로 대체)
  - streamlit (선택)                    : UI 메시지 출력에만 사용; 없어도 동작

【사용 예시】
    from lang_field import LangFieldBuilder

    builder = LangFieldBuilder(openai_client=client, dbg_fn=dbg, dbg_err_fn=dbg_err)
    tag_041, tag_546, orig_title = builder.get_kormarc_tags(item, detail)
    mrk_041 = builder.as_mrk_041(tag_041)
    mrk_546 = builder.as_mrk_546(tag_546)
─────────────────────────────────────────────────────────────────────────────
"""

from __future__ import annotations

import re
import html
import json
import time
import urllib.parse
import concurrent.futures
from collections import defaultdict
from typing import Any, Callable, Dict, List, Mapping, MutableMapping, Optional, Tuple

try:
    import requests
    from bs4 import BeautifulSoup
    _SCRAPER_AVAILABLE = True
except ImportError:
    _SCRAPER_AVAILABLE = False


# ═══════════════════════════════════════════════════════════════
# 1. 상수
# ═══════════════════════════════════════════════════════════════

ISDS_LANGUAGE_CODES: dict[str, str] = {
    'kor': '한국어', 'eng': '영어',  'jpn': '일본어',   'chi': '중국어',
    'rus': '러시아어', 'ara': '아랍어', 'fre': '프랑스어', 'ger': '독일어',
    'ita': '이탈리아어', 'spa': '스페인어', 'por': '포르투갈어', 'tur': '터키어',
    # 확장 언어 (GPT payload 결과에서 자주 등장하는 언어 추가)
    'dut': '네덜란드어', 'gre': '그리스어', 'lat': '라틴어',
    'swe': '스웨덴어',   'nor': '노르웨이어', 'dan': '덴마크어',
    'fin': '핀란드어',   'hun': '헝가리어',   'cze': '체코어',
    'pol': '폴란드어',   'heb': '히브리어',   'per': '페르시아어',
    # 고전 경전·인도 언어
    'san': '산스크리트어', 'pal': '팔리어', 'hin': '힌디어',
    'und': '알 수 없음',
}

ALLOWED_CODES: frozenset[str] = frozenset(ISDS_LANGUAGE_CODES.keys()) - {"und"}

# 한국어 언어명 → ISDS 코드 (Payload 결과 변환용)
_LANG_NAME_TO_ISDS: Dict[str, str] = {
    "영어": "eng", "일본어": "jpn", "중국어": "chi", "러시아어": "rus",
    "프랑스어": "fre", "독일어": "ger", "이탈리아어": "ita",
    "스페인어": "spa", "포르투갈어": "por", "터키어": "tur", "한국어": "kor",
    "아랍어": "ara",
}

# 알라딘 ItemSearch API
_ITEM_SEARCH_URL = "http://www.aladin.co.kr/ttb/api/ItemSearch.aspx"

def _resolve_lang_name_to_isds(lang_name: str) -> "Optional[str]":
    """
    GPT가 반환한 한국어 언어명 → ISDS 코드 변환.
    예) '프랑스어' → 'fre',  '네덜란드어' → 'dut'

    조회 순서
    1) _LANG_NAME_TO_ISDS 직접 매칭
    2) ISDS_LANGUAGE_CODES 역방향(한국어 언어명 → 코드) 직접 매칭
    3) 위 두 테이블에 대해 부분 문자열 탐색 ('현대 영어', '고대 그리스어' 등 대응)
    """
    s = (lang_name or "").strip()
    if not s:
        return None
    # 1) _LANG_NAME_TO_ISDS 직접
    if s in _LANG_NAME_TO_ISDS:
        return _LANG_NAME_TO_ISDS[s]
    # 2) ISDS_LANGUAGE_CODES 역방향 직접 (확장 언어 포함)
    _isds_reverse = {v: k for k, v in ISDS_LANGUAGE_CODES.items() if k != "und"}
    if s in _isds_reverse:
        return _isds_reverse[s]
    # 3) 부분 문자열 탐색
    for name, code in _LANG_NAME_TO_ISDS.items():
        if name in s:
            return code
    for name, code in _isds_reverse.items():
        if name in s:
            return code
    return None


# ── 문자 체계 정규식 (trans.py 이식) ─────────────────────────
_RE_KANA  = re.compile(r"[\u3040-\u309F\u30A0-\u30FF]")
_RE_HAN   = re.compile(r"[\u4E00-\u9FFF]")
_RE_LATIN = re.compile(r"[A-Za-z]")
# 라틴 문자가 아닌 스크립트 — 키릴·아랍·그리스·한글·히브리·태국 등
# 이 패턴이 매칭되면 원제를 라틴어권으로 간주하지 않음
_RE_NON_LATIN = re.compile(
    r"[\u0400-\u04FF"   # 키릴
    r"\u0600-\u06FF"   # 아랍
    r"\u0370-\u03FF"   # 그리스
    r"\uAC00-\uD7A3"   # 한글
    r"\u0590-\u05FF"   # 히브리
    r"\u0E00-\u0E7F"   # 태국
    r"\u3040-\u30FF"   # 히라가나·가타카나
    r"\u4E00-\u9FFF]"  # 한자
)

# ── 전공 → 언어명 규칙 (trans.py 이식) ───────────────────────
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


def _script_weights_on_text(text: str) -> Dict[str, float]:
    """텍스트의 문자 체계(가나·한자·라틴) 가중치 계산 (trans.py 이식)."""
    w: Dict[str, float] = {}
    if not text:
        return w
    if _RE_KANA.search(text):
        w["원제_가나(일본어)"]      = w.get("원제_가나(일본어)", 0.0)      + 2.0
    if _RE_HAN.search(text):
        w["원제_한자(중국어)"]      = w.get("원제_한자(중국어)", 0.0)      + 1.0
        w["원제_한자(일본어)"]      = w.get("원제_한자(일본어)", 0.0)      + 1.0
    if _RE_LATIN.search(text):
        # ★ 라틴은 "영미·유럽권" 레이블로만 — GPT가 직접 구분하게 함
        w["원제_라틴(영미·유럽권)"] = w.get("원제_라틴(영미·유럽권)", 0.0) + 1.5
    return w


def infer_language_from_major_text(major: Optional[str]) -> Optional[str]:
    """전공명 텍스트에서 언어명 추론 (trans.py 이식)."""
    if not major:
        return None
    for pat, lang in _MAJOR_LANG_RULES:
        if re.search(pat, major.strip(), re.I):
            return lang
    return None


def extract_univ_major_regex(text: str) -> Optional[Dict[str, Optional[str]]]:
    """소개글에서 대학/전공 Regex 추출 (trans.py 이식)."""
    if not text or not text.strip():
        return None
    _DEPT = r"(?:학과|전공|학부|어과|어문학과?|문학과|사학과|과)"
    m = re.search(
        r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*"
        r"([가-힣A-Za-z·\s]{2,20}" + _DEPT + r")",
        text,
    )
    if not m:
        m = re.search(
            r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*에서\s*"
            r"([가-힣A-Za-z·\s]{2,20}" + _DEPT + r")",
            text,
        )
    if not m:
        return None
    uni, maj = m.group(1).strip(), m.group(2).strip()
    return {
        "university":        uni,
        "major":             maj,
        "inferred_language": infer_language_from_major_text(maj),
    }


# ═══════════════════════════════════════════════════════════════
# 2. AladinAuthorScraper  — API-First + 웹 크롤링 폴백
# ═══════════════════════════════════════════════════════════════

# ── 역할 판별 상수 ───────────────────────────────────────────────
_TRANSLATOR_ROLE_STRICT: tuple[str, ...] = ("옮긴이", "역자", "옮김", "번역")
_WRITER_ROLE_KEYS:       tuple[str, ...] = (
    "지은이", "지음", "글",
    "엮은이", "엮음", "편자", "편저자", "편저", "편",
    "공저자", "공저", "공동저자",
    "감수",
)

# API subInfo.authors 에서 Bio를 꺼낼 필드 우선순위
_API_BIO_KEYS: tuple[str, ...] = (
    "authorBio", "biography", "authorIntro",
    "intro", "description", "authorDescription", "profile",
)
# item 루트에서 보조 텍스트를 꺼낼 필드
_ITEM_DESC_KEYS: tuple[str, ...] = (
    "fulldescription", "fullDescription", "Story", "story", "toc", "Toc",
)
# wauthor_overview HTML 정제 시 제거할 태그
_BIO_DECOMPOSE_TAGS: tuple[str, ...] = (
    "script", "style", "meta", "noscript", "header", "footer",
    "nav", "aside", "menu", "form", "button", "input", "select",
    "label", "iframe", "link", "ul", "ol", "li", "a",
)
# AuthorSearch href ID 추출용 정규식
_AUTHOR_SEARCH_HREF_RE = re.compile(r"AuthorSearch=(?:[^&]*?@)?(\d+)", re.I)


def _role_is_translator(role: str) -> bool:
    """역자 역할 여부 판별."""
    r = (role or "").strip()
    if not r:
        return False
    if any(m in r for m in _TRANSLATOR_ROLE_STRICT):
        return True
    if "역" in r and not any(x in r for x in ("지은이", "지음", "감수", "교정", "편집")):
        return True
    return False


def _role_is_writer(role: str) -> bool:
    """저자(지은이) 역할 여부 판별."""
    r = (role or "").strip()
    return any(k in r for k in _WRITER_ROLE_KEYS)


def _collect_bio_from_api(item: dict, target_name: str) -> str:
    """
    API item['subInfo']['authors'] 에서 target_name 의 소개글을 수집.
    이름 필터: target_name이 비어 있으면 필터 없이 전체 수집.
    item 루트의 fulldescription/Story 등도 보조 포함.
    """
    chunks: list[str] = []
    sub = item.get("subInfo") or {}

    for auth in sub.get("authors") or []:
        if not isinstance(auth, dict):
            continue
        if target_name:
            if (auth.get("authorName") or "").strip() != target_name.strip():
                continue
        for key in _API_BIO_KEYS:
            val = auth.get(key)
            if isinstance(val, str) and val.strip():
                chunks.append(val.strip())
        # 키 이름이 달라도 긴 문자열이면 소개글로 간주
        for k, v in auth.items():
            if k in ("authorName", "authorId", "authorTypeDesc", "authorTypeName"):
                continue
            if isinstance(v, str) and len(v) > 40:
                chunks.append(v.strip())

    # 책 설명·목차 등 보조 텍스트
    for key in _ITEM_DESC_KEYS:
        v = item.get(key) or sub.get(key)
        if isinstance(v, str) and len(v) > 80:
            chunks.append(v[:5000])

    return "\n\n".join(dict.fromkeys(chunks))


def _extract_author_id_from_api(
    item: dict, target_name: str, want_translator: bool
) -> Optional[int]:
    """subInfo.authors 에서 역할+이름이 일치하는 authorId 반환. 없으면 None."""
    sub = item.get("subInfo") or {}
    for auth in sub.get("authors") or []:
        if not isinstance(auth, dict):
            continue
        if target_name and (auth.get("authorName") or "").strip() != target_name.strip():
            continue
        role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
        if want_translator and not _role_is_translator(role):
            continue
        if not want_translator and not _role_is_writer(role):
            continue
        aid = auth.get("authorId")
        try:
            return int(aid) if aid is not None else None
        except (TypeError, ValueError):
            return None
    return None


def _parse_names_from_raw_author(raw_author: str, want_translator: bool) -> list[str]:
    """subInfo.authors 없을 때 item['author'] 원시 문자열에서 이름 파싱 폴백."""
    names: list[str] = []
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


class AladinAuthorScraper:
    """
    저자/역자 소개글(Bio) 수집기 — API-First + 웹 크롤링 폴백.

    수집 우선순위
    ─────────────────────────────────────────────────────────────
    1순위 (API)      item['subInfo']['authors'][n]['authorBio'] 등
                     → 네트워크 요청 0회
    2순위 (웹·ID)    API에 authorId 있으면 wauthor_overview 크롤링
                     → 네트워크 요청 1회
    3순위 (웹·HTML)  API에 authorId 없으면 wproduct 상세 HTML에서
                     이름 매칭으로 ID를 파싱한 뒤 wauthor_overview 크롤링
                     → 네트워크 요청 최대 2회
    """

    _WPRODUCT_BASE  = "https://www.aladin.co.kr/shop/wproduct.aspx"
    _OVERVIEW_BASE  = "https://www.aladin.co.kr/author/wauthor_overview.aspx"
    _ITEM_SEARCH    = _ITEM_SEARCH_URL
    _HEADERS: dict[str, str] = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
        ),
        "Accept":          "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8",
        "Referer":         "https://www.aladin.co.kr/",
    }
    _TIMEOUT    = 10
    _RETRY      = 2
    _RETRY_WAIT = 1.0

    # ── HTTP 헬퍼 ─────────────────────────────────────────────

    def _get(self, url: str, params: Optional[dict] = None) -> Optional["requests.Response"]:
        """재시도 포함 GET. 실패 시 None."""
        if not _SCRAPER_AVAILABLE:
            return None
        for attempt in range(self._RETRY):
            try:
                resp = requests.get(
                    url, params=params,
                    headers=self._HEADERS, timeout=self._TIMEOUT,
                )
                resp.raise_for_status()
                return resp
            except Exception:
                if attempt < self._RETRY - 1:
                    time.sleep(self._RETRY_WAIT)
        return None

    # ── 상세 페이지 기반 AuthorId 파싱 ───────────────────────

    @staticmethod
    def _extract_id_from_href(href: str) -> Optional[int]:
        """href에서 AuthorSearch=…@숫자 패턴으로 ID 추출."""
        if not href or "AuthorSearch=" not in href:
            return None
        m = _AUTHOR_SEARCH_HREF_RE.search(href)
        if not m:
            return None
        try:
            return int(m.group(1))
        except (TypeError, ValueError):
            return None

    def _resolve_id_from_html(self, html: str, target_name: str) -> Optional[int]:
        """
        wproduct 상세 HTML에서 AuthorSearch= 링크를 순회하며
        앵커 텍스트가 target_name과 정확히 일치하는 항목의 ID 반환.
        """
        t = (target_name or "").strip()
        if not t or not html or not _SCRAPER_AVAILABLE:
            return None
        soup = BeautifulSoup(html, "html.parser")
        for anchor in soup.find_all("a", href=True):
            href = anchor.get("href") or ""
            if "AuthorSearch=" not in href:
                continue
            text = re.sub(r"\s+", " ", anchor.get_text(separator=" ", strip=True)).strip()
            if text != t:
                continue
            aid = self._extract_id_from_href(href)
            if aid is not None:
                return aid
        return None

    def _scrape_author_id_from_product(
        self, item: dict, target_name: str
    ) -> Optional[int]:
        """
        item에서 ItemId(또는 isbn13)를 구해 wproduct 상세 페이지를 fetch한 뒤
        target_name과 일치하는 저자 링크의 ID 반환. 실패 시 None.
        """
        if not _SCRAPER_AVAILABLE:
            return None
        pid: Optional[str] = None
        for key in ("itemId", "item_id"):
            v = (item or {}).get(key)
            if v is not None and str(v).strip():
                pid = str(v).strip()
                break
        if not pid:
            isbn = (
                (item or {}).get("isbn13") or (item or {}).get("isbn") or ""
            ).replace("-", "").strip()
            pid = isbn or None
        if not pid:
            return None
        resp = self._get(self._WPRODUCT_BASE, params={"ItemId": pid})
        if resp is None:
            return None
        return self._resolve_id_from_html(resp.text, target_name)

    # ── wauthor_overview 크롤링 ──────────────────────────────

    def scrape_author_bio_from_overview(self, author_id: int) -> str:
        """wauthor_overview.aspx에서 소개글 크롤링. 노이즈 태그 제거 후 p·리프 div 수집."""
        if not _SCRAPER_AVAILABLE or not author_id:
            return ""
        resp = self._get(self._OVERVIEW_BASE, params={"AuthorSearch": f"@{author_id}"})
        if resp is None:
            return ""
        soup = BeautifulSoup(resp.text, "html.parser")
        for tag_name in _BIO_DECOMPOSE_TAGS:
            for el in soup.find_all(tag_name):
                el.decompose()
        root = soup
        for attr, pattern in (
            ("id",    re.compile(r"author|writer|profile|bio", re.I)),
            ("class", re.compile(r"author|writer|profile|bio|intro", re.I)),
        ):
            found = soup.find(attrs={attr: pattern})
            if found is not None:
                root = found
                break
        chunks: list[str] = []
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
        bio_text = "\n\n".join(dict.fromkeys(chunks))
        if not bio_text and root is not soup:
            for p in soup.find_all("p"):
                t = p.get_text(separator=" ", strip=True)
                if len(t) >= 8:
                    chunks.append(t)
            bio_text = "\n\n".join(dict.fromkeys(chunks))
        return bio_text[:1500] if bio_text else ""

    # ── 공개 인터페이스 ──────────────────────────────────────

    def fetch_bios(self, item: dict) -> tuple[dict[str, str], str]:
        """
        API-First 방식으로 저자·역자 Bio를 수집.

        반환
        ----
        (author_bios, translator_bio)
          · author_bios    : {저자명: bio_text} — 저자별 Bio 매핑 dict
          · translator_bio : 역자 Bio 문자열 (기존과 동일)

        수집 파이프라인 (저자·역자 각각 독립 실행)
        ──────────────────────────────────────────
        Step 1  API 소개글 (_collect_bio_from_api)
                → 결과가 있으면(> 5자) 즉시 반환, 네트워크 요청 0회
        Step 2  API authorId 있음 → scrape_author_bio_from_overview
        Step 3  API authorId 없음 → wproduct HTML 이름 매칭으로 ID 파싱
                → scrape_author_bio_from_overview
        """
        item = item or {}
        sub  = item.get("subInfo") or {}
        authors_list = [a for a in (sub.get("authors") or []) if isinstance(a, dict)]

        # 저자(지은이) 이름 목록
        writer_names: list[str] = []
        for auth in authors_list:
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _role_is_writer(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    writer_names.append(n)
        if not writer_names:
            writer_names = _parse_names_from_raw_author(
                item.get("author") or "", want_translator=False
            )

        # 역자 이름 목록
        translator_names: list[str] = []
        for auth in authors_list:
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _role_is_translator(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    translator_names.append(n)
        if not translator_names:
            translator_names = _parse_names_from_raw_author(
                item.get("author") or "", want_translator=True
            )

        # 저자별 Bio를 각각 독립 수집 (최대 4명, 병렬)
        def _fetch_one_author(name: str) -> tuple[str, str]:
            """단일 저자 Bio 수집 — (이름, bio) 반환."""
            bio = self._fetch_single_bio(item, [name], False)
            return name, bio

        author_bios: dict[str, str] = {}
        target_names = writer_names[:4]
        if not target_names:
            pass  # 저자 없음 → author_bios 빈 dict 유지
        elif len(target_names) == 1:
            # 저자 1명: 기존 방식과 동일
            bio = self._fetch_single_bio(item, target_names, False)
            author_bios = {target_names[0]: bio}
        else:
            # 저자 2~4명: 병렬 수집
            with concurrent.futures.ThreadPoolExecutor(max_workers=min(len(target_names), 4)) as ex:
                futures = {ex.submit(_fetch_one_author, n): n for n in target_names}
                for fut in concurrent.futures.as_completed(futures):
                    name, bio = fut.result()
                    author_bios[name] = bio

        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
            future_trans  = executor.submit(
                self._fetch_single_bio, item, translator_names, True
            )
            translator_bio = future_trans.result()

        return author_bios, translator_bio

    def _fetch_single_bio(
        self,
        item: dict,
        names: list[str],
        want_translator: bool,
    ) -> str:
        """
        names 목록을 순서대로 시도해 비지 않은 Bio 하나를 반환.

        Step 1  API 소개글 (네트워크 요청 없음)
        Step 2  API authorId 있음 → wauthor_overview 크롤링
        Step 3  API authorId 없음 → wproduct HTML 이름 매칭 → wauthor_overview 크롤링
        """
        for name in names[:4]:   # 공동저자·공편자 최대 4명까지 시도
            # Step 1 — API 소개글 (네트워크 요청 없음)
            api_bio = _collect_bio_from_api(item, name)
            if api_bio.strip() and len(api_bio.strip()) > 5:
                return api_bio.strip()

            if not _SCRAPER_AVAILABLE:
                continue

            # Step 2 — API authorId로 바로 크롤링
            aid = _extract_author_id_from_api(item, name, want_translator)

            # Step 3 — API authorId 없으면 상세 페이지 HTML에서 파싱
            if aid is None:
                aid = self._scrape_author_id_from_product(item, name)

            if aid is None:
                continue

            web_bio = self.scrape_author_bio_from_overview(aid)
            if web_bio.strip():
                return web_bio.strip()

        return ""

# ═══════════════════════════════════════════════════════════════
# 3. LangFieldBuilder
# ═══════════════════════════════════════════════════════════════

class LangFieldBuilder:
    """
    041 / 546 필드 생성 전담 클래스.

    Parameters
    ----------
    openai_client
        OpenAI() 인스턴스.  None이면 GPT 호출을 건너뛰고 'und'를 반환.
    model
        사용할 GPT 모델명.  기본값 'gpt-4o'.
    dbg_fn
        디버그 메시지 출력 함수.  기본값 print.
    dbg_err_fn
        에러 메시지 출력 함수.  기본값 print.
    """

    # ─────────────────────────────────────────────
    # CONFIG: 키워드 딕셔너리 (한 곳에서 관리)
    # ─────────────────────────────────────────────

    # 문학 판정 키워드
    LIT_KEYWORDS: dict[str, list[str]] = {
        "ko": ["문학", "소설", "시", "희곡"],
        "en": ["literature", "fiction", "novel", "poetry", "poem", "drama", "play"],
    }

    # 비문학 오버라이드 키워드
    NONFICTION_KEYWORDS: dict[str, list[str]] = {
        "ko": ["역사", "근현대사", "서양사", "유럽사", "전기", "평전",
               "사회", "정치", "철학", "경제", "경영", "인문", "에세이", "수필"],
        "en": ["history", "biography", "memoir", "politics", "philosophy",
               "economics", "science", "technology", "nonfiction", "essay", "essays"],
    }

    # SF 보호 대상: 문학 최상위일 때 비문학 오버라이드에서 제외할 키워드
    SF_GUARD_KEYWORDS: dict[str, list[str]] = {
        "ko": ["과학", "기술"],
        "en": ["science", "technology"],
    }

    # 카테고리 → 언어 힌트 매핑 (detect_language_from_category용)
    CATEGORY_LANG_MAP: list[tuple[list[str], str]] = [
        (["일본"],                        "jpn"),
        (["중국"],                        "chi"),
        (["영미", "영어", "아일랜드"],     "eng"),
        (["프랑스"],                       "fre"),
        (["독일", "오스트리아"],           "ger"),
        (["러시아"],                       "rus"),
        (["이탈리아"],                     "ita"),
        (["스페인"],                       "spa"),
        (["포르투갈"],                     "por"),
        (["튀르키예", "터키"],             "tur"),
    ]

    def __init__(
        self,
        openai_client=None,
        model: str = "gpt-4o",
        dbg_fn:     Optional[Callable] = None,
        dbg_err_fn: Optional[Callable] = None,
    ):
        self._client  = openai_client
        self._model   = model
        self._dbg     = dbg_fn     or (lambda *a: print("[DBG]",  *a))
        self._dbg_err = dbg_err_fn or (lambda *a: print("[ERR]",  *a))
        self._scraper = AladinAuthorScraper()

    # ─────────────────────────────────────────────
    # 2-1. GPT 판정 함수
    # ─────────────────────────────────────────────

    def gpt_guess_from_original_title_only(self, original_title: str) -> str:
        """
        라틴 알파벳으로만 이루어진 원제(Original Title)의 언어를 경량 GPT로 판별.

        비문학 파이프라인 1.5단계에서 호출된다:
          유니코드 조기 반환(1단계)이 und/eng일 때, 원제가 순수 라틴 문자인 경우만 실행.
          → 확정(und 외 코드) 반환 시 Bio 크롤링·GPT Payload(2단계) 완전 스킵.
          → und 반환 시 2단계로 계속 진행.

        호출 전제 조건 (파이프라인에서 보장, 메서드 내부에서도 재확인):
          - 원제에 라틴 알파벳이 1자 이상 포함
          - 원제에 한자·가나·키릴·아랍 등 비라틴 스크립트가 없음

        판별 방식: 엄격한 단어 단위 사전 매칭 + 앵커 단어 우선 규칙
          - 글자·억양 기호 단위 추론 절대 금지
          - 앵커 단어(특정 언어 사전에만 존재하는 고유 어휘)가 하나라도 있으면
            나머지 단어의 모호성과 무관하게 해당 언어로 즉시 확정
          - 앵커 단어가 없고 모든 단어가 다중 언어에 걸쳐 쓰이면 'und'
        """
        if not self._client:
            return "und"
        title = (original_title or "").strip()
        if not title:
            return "und"

        # 라틴 문자 전용 가드 — 비라틴 스크립트가 섞인 원제는 처리하지 않음
        if not _RE_LATIN.search(title) or _RE_NON_LATIN.search(title):
            self._dbg(
                f"🔬 [원제GPT] '{title}' — 비라틴 문자 포함 또는 라틴 없음 → 스킵"
            )
            return "und"

        system_prompt = (
            "당신은 라틴 문자권 원제(Original Title)의 언어를 판별하는 전문가입니다.\n"
            "판별 방법은 단 하나, '각 단어가 해당 언어의 공식 어휘 사전에 온전히 등재되어 있는가'를 "
            "1:1로 대조하는 것입니다.\n\n"

            "【자동 탈락(Failure) 조건】\n"
            "아래 행위를 하면 즉시 틀린 판정으로 간주합니다.\n"
            "- 억양 기호(à, è, é, ø, ë 등)나 철자(letters)의 생김새·모양을 근거로 삼는 것\n"
            "- 글자가 '~어처럼 보인다'는 시각적 유추를 하는 것\n"
            "- 단어 전체가 사전에 없는데도 철자 구조로 언어를 추측하는 것\n"
            "- 문맥을 무시하고 명백한 영어 문장을 und로 반환하는 것\n"
            "- #reason이 여는 대괄호 '[' 로 시작하지 않거나 단어 검증 과정을 건너뛰고\n"
            "  결론만 쓰는 것 (이는 시스템 지침 위반이며 즉시 탈락(Failure))\n"
            "- 만장일치(100%) 영어 단어들을 보고 '여러 언어 사전에 있다' 혹은\n"
            "  '60%를 넘지 않는다'고 거짓 보고하는 할루시네이션\n"
            "  ★ 'What', 'We', 'Cannot', 'Know' 가 전부 영어인데 und를 뱉는 것은\n"
            "    명백한 거짓말이며 탈락(Failure)입니다. 즉시 eng를 출력하십시오.\n"
            "위 모든 항목은 결과와 무관하게 자동 탈락(Failure)입니다.\n\n"

            "【분석 절차】\n"
            "1. 단어 분리: 원제를 공백 기준으로 개별 단어로 쪼개십시오.\n"
            "   예) 'Une aspiration au dehors' → ['Une', 'aspiration', 'au', 'dehors']\n\n"

            "2. 사전 대조(1:1 매칭): 각 단어를 공식 어휘 사전과 1:1로 대조하십시오.\n"
            "   - 단어 전체가 사전 어휘로 존재해야만 '매칭 성공'입니다.\n"
            "   - 사전에 없거나 불확실한 단어는 '미확인'으로 분류하십시오.\n"
            "   - 매칭된 단어마다 '어느 언어 사전에 있는지' 전부 기록하십시오.\n"
            "   ★ 암산 금지: 2단계 결과는 #reason의 대괄호 안에 반드시 전부 적어야 합니다.\n\n"

            "3. 【최최우선】1단어 원제 특별 규칙:\n"
            "   원제가 단 1개의 단어로만 이루어진 경우, 비율 계산·기능어 체크를 하지 마십시오.\n"
            "   - 해당 단어가 특정 언어 1곳의 사전에만 존재하면 즉시 해당 언어로 확정.\n"
            "   - 단어가 여러 언어 사전에 공통으로 쓰이는 모호어(예: 'Chat', 'De', 'Sport')이면\n"
            "     'und'로 처리하고 다른 규칙을 적용하지 마십시오.\n"
            "   ★ 절대 금지: 1단어를 보고 '60% 미만이다' 혹은 '앵커가 없다'고 말하는 것.\n"
            "     1단어는 100% 아니면 und입니다. 비율 계산 자체가 성립하지 않습니다.\n"
            "   - 예: [Proof(eng)] → 단어 1개, eng 사전에 존재 → 즉시 eng 확정\n"
            "   - 예: [Chat(fre/eng)] → 다국어 공통어 → und\n\n"

            "4. 【최우선】기능어 앵커 (다국어 중첩 기능어 교차 검증 포함):\n"
            "   전치사·관사·접속사 등 특정 언어 고유의 기능어(Functional Words)가 하나라도\n"
            "   있으면 다른 단어들이 외래어로 겹치든 무관하게 즉시 해당 언어로 확정하십시오.\n"
            "   기능어는 어휘 단어보다 훨씬 강력한 언어 식별자입니다.\n\n"
            "   ★★ 중요 예외 — 다국어 중첩 기능어(Multilingual Homograph) 처리 ★★\n"
            "   아래 기능어들은 영어·라틴어·프랑스어·스페인어 등 여러 언어에서 철자가 완벽히\n"
            "   동일하므로, 단독으로 발견되었을 때 즉시 확정하지 말고 교차 검증을 먼저 수행:\n"
            "     중첩 기능어 목록: in, de, per, et, pro, a, ad, ex, cum, ab\n\n"
            "   [교차 검증 절차 — 중첩 기능어가 발견된 경우]\n"
            "   Step A. 라틴어 격변화(굴절 어미) 검사:\n"
            "     중첩 기능어 뒤에 오는 명사/형용사가 아래 라틴어 격어미를 가지면 → lat 확정\n"
            "     라틴어 격어미 패턴:\n"
            "       -am, -um, -em  (대격 단수)\n"
            "       -o, -ae, -i    (여격/속격 단수)\n"
            "       -is, -ibus     (탈격·여격 복수)\n"
            "       -orum, -arum   (속격 복수)\n"
            "     예: 'In memoriam' → 'memoriam'의 -am은 라틴어 대격 어미 → lat 확정\n"
            "     예: 'De Officiis' → 'Officiis'의 -is는 라틴어 탈격 복수 어미 → lat 확정\n"
            "     예: 'Ad Astra' → 'Astra'의 -a는 라틴어 중성 복수 어미 → lat 확정\n\n"
            "   Step B. 라틴어 학술·역사 관용구(Collocation) 검사:\n"
            "     단어 조합 전체가 역사적·학술적으로 정착된 라틴어 관용구인지 확인:\n"
            "     예: 'Pro et contra' → et(라틴어 접속사)+라틴어 관용구 전체 → lat 확정\n"
            "     예: 'De jure' → 라틴어 법률 관용구 → lat 확정\n"
            "     예: 'Per aspera ad astra' → 라틴어 격언 → lat 확정\n\n"
            "   Step C. 나머지 단어 언어 분포 확인:\n"
            "     중첩 기능어 외 다른 단어들이 명백히 특정 언어에만 속하면 그 언어로 확정.\n"
            "     예: 'in Cold Blood' → 'Cold'(eng)·'Blood'(eng) → 'in'은 eng 기능어 → eng 확정\n"
            "     예: 'De Bourgondiërs' → 'Bourgondiërs'(dut 단독) → 'de'는 dut 기능어 → dut 확정\n\n"
            "   Step D. 교차 검증 후에도 미확정이면 중첩 기능어를 앵커로 인정하지 않고\n"
            "     다음 규칙(5번 만장일치·6번 다수결·7번 단독 앵커)으로 넘어가십시오.\n\n"
            "   [비중첩 기능어 — 즉시 확정 대상]\n"
            "   아래 기능어들은 단독으로도 즉시 해당 언어 확정:\n"
            "   - 영어 전용:  the, an, how, and, on, at, into, with, of, for,\n"
            "                 by, from, it, is, are, was, were, to, or, but, if, as,\n"
            "                 this, that, about, after, before, through, up, out\n"
            "                 ★ 대소문자 무관: 'The', 'And', 'Of' 모두 eng 기능어\n"
            "   - 프랑스어:   une, au, aux, du, des, les, dans, sur, pour, par, avec,\n"
            "                 sans, sous, dont, qui, que, mais, donc\n"
            "   - 이탈리아어: della, delle, degli, nel, nella, dal, dalla, sul, sulla,\n"
            "                 tra, fra, uno, gli, questo, questa\n"
            "   - 스페인어:   del, los, las, unos, con, sin, sobre, desde, hasta, para,\n"
            "                 pero, sino, aunque, porque\n"
            "   - 네덜란드어: het, een, van, voor, naar, met, over, aan, bij, uit, door\n"
            "   - 독일어:     der, die, das, ein, eine, und, oder, aber, denn, weil,\n"
            "                 dass, wenn, als, durch, für, mit, von, bei, nach, über\n"
            "   - 예: 'The Formula How Rogues and Speed Freaks Reengineered F1'\n"
            "         → 'the'·'and' 는 영어 전용 기능어 → 즉시 eng 확정\n"
            "   - 예: 'A Naturalist at Large'\n"
            "         → 'at'은 영어 전용, 'a'는 중첩이므로 'at' 단독으로 eng 확정\n"
            "   - 예: 'In Cold Blood' → 'in'은 중첩 기능어 → Step C 검사\n"
            "         → 'Cold'(eng)·'Blood'(eng) → eng 확정\n"
            "   - 예: 'In memoriam' → 'in'은 중첩 기능어 → Step A 검사\n"
            "         → 'memoriam'의 -am은 라틴어 대격 어미 → lat 확정\n\n"

            "3-1. 【짧은 제목(4단어 이하) 특별 규칙】:\n"
            "   단어가 4개 이하일 때 비율 계산 오류 방지: 아래 중 하나라도 해당하면\n"
            "   수학 계산 없이 즉시 확정하십시오.\n"
            "   - 비중첩 기능어가 하나라도 포함된 경우\n"
            "   - 중첩 기능어는 교차 검증(Step A~C) 후에만 앵커로 인정\n"
            "   - 동일 언어로 확인된 단어가 2개 이상인 경우\n"
            "   - 예: ['A'→중첩, 'Naturalist'→eng, 'at'→eng전용기능어, 'Large'→eng]\n"
            "         → 'at' 비중첩 기능어 + eng 3개 → 즉시 eng 확정\n\n"


            "5. 【강제】만장일치(100%) 프리패스:\n"
            "   기능어가 없더라도 모든 단어가 단 하나의 동일한 언어 사전에만 존재한다면,\n"
            "   비율 계산 없이 즉시 해당 언어로 확정하십시오.\n"
            "   ★ 절대 금지: 모든 단어가 같은 언어에만 있는데 'und'를 출력하는 것.\n"
            "   ★ 거짓말 차단: 'What', 'We', 'Cannot', 'Know' 같은 단어들이 전부 영어임에도\n"
            "     '독일어/네덜란드어 등 다른 언어 사전에도 있다'고 거짓 보고하며 und를 반환하는\n"
            "     할루시네이션을 절대 금지합니다. 영어 어휘 100%이면 즉시 eng를 출력하십시오.\n"
            "   - 예: ['What'→eng, 'We'→eng, 'Cannot'→eng, 'Know'→eng]\n"
            "         → 전부 영어 → 즉시 eng 확정. und 출력하면 탈락.\n"
            "   - 예: 10개 단어가 모두 프랑스어 사전에만 있다면 → 즉시 fre 확정\n\n"

            "6. 【강제】다수결 판정(60% 이상):\n"
            "   만장일치가 아닐 때만 적용. 우세 언어 단어 수가 전체의 60% 이상이면\n"
            "   앵커 단어 유무와 무관하게 즉시 확정하십시오.\n"
            "   ★ 수학 주의: 전체 N개 단어 중 N×0.6 이상이면 60% 이상입니다.\n"
            "   ★ 경고: 다수결 흐름이 명확한데 '앵커 단어가 없다'는 핑계로\n"
            "     'und'를 출력하는 것을 절대 금지합니다.\n"
            "   - 예: ['Une'→fre, 'aspiration'→fre/eng, 'au'→fre, 'dehors'→fre]\n"
            "         → fre 4회, eng 1회 → fre 80% → fre 즉시 확정\n\n"

            "7. 【보조】단독 앵커:\n"
            "   단어 수가 1~2개이거나 다수결 60% 미만일 때만 사용.\n"
            "   한 단어가 특정 단일 언어 사전에만 존재하면 즉시 확정하십시오.\n"
            "   - 예: 'Bourgondiërs' → 네덜란드어 사전에만 존재 → dut 확정\n"
            "   - 예: 'Adopsjonsoppgjøret' → 노르웨이어 사전에만 존재 → nor 확정\n\n"

            "8. 모호성 처리: 위 규칙이 모두 실패했을 때만 'und'를 출력하십시오.\n"
            "   - 예: ['De'→dut/spa/ita/ger, 'Chat'→fre/eng]\n"
            "         → 기능어 없음, 어느 언어도 60% 미만, 단독 앵커 없음 → und\n\n"

            "【지원 ISDS 코드】\n"
            "eng, fre, dut, spa, por, ger, ita, swe, nor, dan, fin, pol, cze, hun, rum, lat, gre, und\n\n"

            "【출력 형식】(정확히 2~3줄, 다른 텍스트 절대 금지)\n"
            "★ 반드시 #reason을 첫 줄에 쓰고, $h를 마지막 줄에 쓸 것.\n"
            "★ $h를 #reason보다 먼저 쓰면 즉시 탈락(Failure).\n\n"
            "#reason=[← 반드시 여는 대괄호 '[' 로 시작할 것. 시작하지 않으면 탈락(Failure).\n"
            "  각 단어의 매칭 결과를 빠짐없이 나열한 뒤 '->' 로 결론을 쓸 것.\n"
            "  형식: [단어1(언어,기능어여부), 단어2(언어), 단어3(언어/미확인), ...] -> 결론 1문장\n"
            "  예1: [A(eng,기능어), Naturalist(eng), at(eng,기능어), Large(eng)] -> 기능어 2개+eng 100%, eng 확정]\n"
            "  예2: [What(eng), We(eng), Cannot(eng), Know(eng)] -> 만장일치 eng 100%, eng 확정]\n"
            "  예3: [De(dut/spa/ita/ger), Chat(fre/eng)] -> 기능어 없음, 어느 언어도 60% 미만, und]\n"
            "#signals=[감지된 기능어 또는 앵커 단어, 콤마로 구분]  (선택)\n"
            "$h=[#reason에서 내린 결론과 반드시 일치하는 ISDS 코드 또는 und]"
        )

        user_prompt = f'원제: "{title}"'

        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user",   "content": user_prompt},
                ],
                temperature=0,
                max_tokens=300,   # CoT 단어별 나열 + 결론 여유 확보
            )
            content = (resp.choices[0].message.content or "").strip()
            code, reason, signals = _extract_code_and_reason(content, "$h")

            # und는 정상적인 '판단 보류' 결과 — ALLOWED_CODES 체크를 거치되
            # und는 허용(다음 단계로 위임)
            if code != "und" and code not in ALLOWED_CODES:
                self._dbg(
                    f"🔬 [원제GPT] 알 수 없는 코드 '{code}' → und 처리"
                )
                code = "und"

            self._dbg(f"🔬 [원제GPT] '{title}' → $h={code}")
            if reason:  self._dbg(f"🔬 [원제GPT] 이유: {reason}")
            if signals: self._dbg(f"🔬 [원제GPT] 단서: {signals}")
            return code

        except Exception as e:
            self._dbg_err(f"GPT 오류 (gpt_guess_from_original_title_only): {e}")
            return "und"

    def gpt_guess_main_lang(
        self,
        title: str,
        category: str,
        publisher: str,
        description: str = "",
        author_info: str = "",
    ) -> str:
        """
        본문 언어($a) 추정.

        외국어·수험서 카테고리의 어학 교재·대역 문고 등
        다중 언어 병용 도서를 올바르게 판정하기 위해
        description·author_info를 추가 단서로 활용.

        반환: 단일 코드('kor') 또는 쉼표 구분 다중 코드('jpn, kor').
              불확실하면 'und'.
        """
        if not self._client:
            return "und"

        system_prompt = (
            "당신은 KORMARC 041 필드(언어코드) 생성을 위한 도서 언어 판정 전문가입니다.\n"
            "알라딘 등의 서지 데이터에서 제공되는 도서의 본문 언어(041 $a)를 "
            "ISDS 코드로 정확하게 판정하는 것이 목표입니다.\n\n"

            "[판정 지침]\n"
            "1. 단순 제목/카테고리 의존 금지:\n"
            "   제목에 한글이 있어도, description과 저자/역자 정보를 분석하여 "
            "실제 본문을 구성하는 언어를 파악하십시오.\n"
            "   ★ 절대 금지: '국내도서' 카테고리이거나 제목에 한글이 있다는 이유만으로 "
            "무조건 kor로 확정하는 행위.\n\n"

            "2. 다중 언어 병기(혼용) 허용:\n"
            "   외국어 지문·원문과 한국어 해설·번역이 함께 제공되는 학습서, 수험서, "
            "대역 문고의 경우 반드시 두 언어를 모두 판별하여 병기하십시오.\n"
            "   비중이 높은 핵심 학습 언어(외국어)를 먼저 배치하고, "
            "보조 언어(한국어)를 뒤에 배치하십시오.\n"
            "   예: 일본어 원문 + 한국어 해설 → jpn, kor\n\n"

            "3. description 키워드 적극 활용:\n"
            "   '대역', '원서 읽기', '단어장', '해설', 'N3 대비', '지문 수록', "
            "'원문과 번역' 등의 표현이 있으면 다중 언어 병기 여부를 즉시 판단하십시오.\n\n"

            "4. 카테고리별 기본 판정 가이드:\n"
            "   · 국내도서>외국어>일본어   : description에 별도 단서 없으면 jpn, kor\n"
            "   · 국내도서>외국어>영어     : description에 별도 단서 없으면 eng, kor\n"
            "   · 국내도서>수험서>어학(영어): description에 별도 단서 없으면 eng, kor\n"
            "   · 국내도서>외국어>중국어   : description에 별도 단서 없으면 chi, kor\n"
            "   · 국내도서>소설/시 등 일반 : description에 외국어 단서 없으면 kor\n\n"
            "   ★★ 카테고리보다 제목·description의 실제 언어 단서를 반드시 우선:\n"
            "   카테고리명이 '영어독해'·'영어'라도 제목이나 description에\n"
            "   일본어(가나·한자)·중국어·프랑스어 등 다른 언어가 명시되어 있으면\n"
            "   카테고리를 무시하고 실제 언어를 우선 판정하십시오.\n"
            "   절대 금지: 카테고리 이름만 보고 실제 본문 언어를 덮어쓰는 행위.\n"
            "   예: 카테고리='외국어>영어독해', 제목='星の王子さま(어린 왕자 일본어판)'\n"
            "     → 제목에 일본어(가나)가 명시됨 → jpn, kor (eng 절대 아님)\n"
            "   예: 카테고리='외국어>영어독해', description='일본어 원문과 한국어 번역 수록'\n"
            "     → description 단서 우선 → jpn, kor\n\n"

            "5. 외국어·어학수험서 카테고리가 아닌 경우 기본값:\n"
            "   카테고리가 외국어·어학수험서가 아닌 일반 카테고리(소설, 경제경영, 역사,\n"
            "   인문학, 컴퓨터, 요리 등)이고, description에도 외국어 지문·원문 혼용\n"
            "   단서가 전혀 없다면 kor로 판정하십시오.\n"
            "   이 경우 GPT가 임의로 외국어 가능성을 열어두는 것은 오판입니다.\n\n"

            "[출력 형식] (엄격히 준수)\n"
            "$a=[ISDS 코드. 2개 이상이면 콤마로 구분: jpn, kor]\n"
            "#reason=[description 및 카테고리를 바탕으로 한 짧은 근거]\n"
            "#signals=[대역, 해설, 외국어 원문 등 결정적 단서] (선택)\n\n"

            "[판정 예시]\n"
            "입력: 제목 '어린 왕자 일본어판', 분류 '국내도서>외국어>일본어', "
            "description '일본어 원문과 한국어 번역을 나란히 배치하여...'\n"
            "출력:\n"
            "$a=[jpn, kor]\n"
            "#reason=[일본어 원문과 한국어 번역이 대역으로 혼용된 어학 학습서]\n"
            "#signals=[일본어 원문, 한국어 번역, 대역]\n\n"
            "입력: 제목 '해커스 토익 Reading', 분류 '국내도서>수험서>어학', "
            "description '최신 토익 영문 지문 수록 및 상세한 한글 해설 제공'\n"
            "출력:\n"
            "$a=[eng, kor]\n"
            "#reason=[영어 지문과 한국어 해설이 혼용된 수험서]\n"
            "#signals=[영문 지문, 한글 해설]"
        )

        user_content = (
            f"- 제목: {title}\n"
            f"- 분류: {category}\n"
            f"- 출판사: {publisher}\n"
        )
        if author_info:
            user_content += f"- 저자/역자 정보: {author_info}\n"
        if description:
            user_content += f"- 도서 상세글: {description[:800]}\n"

        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user",   "content": user_content.strip()},
                ],
                temperature=0,
                max_tokens=200,
            )
            content = (resp.choices[0].message.content or "").strip()
            code, reason, signals = _extract_code_and_reason(content, "$a")

            # 다중 언어 처리: "jpn, kor" → 각 코드 검증 후 재조합
            codes = [c.strip() for c in code.split(",") if c.strip()]
            valid_codes = [c for c in codes if c in ALLOWED_CODES]
            final_code = ", ".join(valid_codes) if valid_codes else "und"

            self._dbg(f"🧭 [GPT 본문언어] $a={final_code}")
            if reason:  self._dbg(f"🧭 [이유] {reason}")
            if signals: self._dbg(f"🧭 [단서] {signals}")
            return final_code
        except Exception as e:
            self._dbg_err(f"GPT 오류 (gpt_guess_main_lang): {e}")
            return "und"

    # ─────────────────────────────────────────────
    # 2-1a-2. GPT 내부 지식 기반 보완 추론 (2-b단계)
    # ─────────────────────────────────────────────

    def gpt_guess_by_author_knowledge(
        self,
        author_name: str,
        translator_name: str = "",
        has_translator: bool = False,
        title: str = "",
        original_title: str = "",
    ) -> str:
        """
        Bio 크롤링 성공했지만 소개글에서 국적 단서를 못 찾았을 때,
        GPT의 학습 데이터(내부 지식)를 활용한 2차 보완 추론.

        할루시네이션 방지:
          - '모르면 반드시 und'를 명시
          - 역자 이름 단독으로 원서 언어 단정 금지
        """
        if not self._client or not author_name.strip():
            return "und"

        translator_line = (
            f"- 역자: {translator_name} (역자가 있으므로 번역서임. "
            "역자 이름만으로 원서 언어를 단정하지 말 것.)"
            if has_translator and translator_name.strip()
            else "- 역자: 없음"
        )
        original_title_line = (
            f"- 원제: {original_title}" if original_title.strip() else ""
        )
        title_line = f"- 제목(한국어): {title}" if title.strip() else ""

        prompt = f"""
아래 저자를 당신이 알고 있다면, 그 지식을 바탕으로 원서 언어(041 $h)를 추정하십시오.

입력 정보:
- 저자: {author_name}
{original_title_line}
{title_line}
{translator_line}

판단 지침:
- 이 저자를 알고 있다면: 국적·주요 집필 언어·대표작의 최초 출간 언어를 먼저 서술하고,
  그것을 근거로 원서 언어를 판단하십시오.
- 이 저자를 모르거나 확신이 없다면: 반드시 'und'를 출력하십시오.
  절대 금지: 모르는 저자를 억지로 추정하는 할루시네이션.
- 원제가 제공된 경우 문자 체계(가나·한자·라틴 등)를 추가 단서로 활용하십시오.
- 역자가 있어도 '역자가 한국인이므로 kor'라는 논리는 절대 금지.
- 가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur, und

출력형식:
$h=[ISDS 코드 또는 und]
#reason=[알고 있는 정보 요약 또는 '이 저자를 알 수 없어 und 반환']
""".strip()

        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": "저자 사전 지식 기반 원서 언어 추정기"},
                    {"role": "user",   "content": prompt},
                ],
                temperature=0,
                max_tokens=150,
            )
            content = (resp.choices[0].message.content or "").strip()
            code, reason, _ = _extract_code_and_reason(content, "$h")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"📘 [2-b단계/지식추론] $h={code} | {reason[:80] if reason else ''}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류 (gpt_guess_by_author_knowledge): {e}")
            return "und"

    # ─────────────────────────────────────────────
    # 2-1b. JSON Payload 빌더 (trans.py 이식)
    # ─────────────────────────────────────────────

    @staticmethod
    def _build_book_info(item: Dict, original_title: str) -> Dict[str, Any]:
        """
        GPT payload용 도서 메타데이터 묶음.
        (trans.py build_book_info_from_item 이식)
        """
        sub = item.get("subInfo") or {}
        desc_parts: List[str] = []
        for key in ("fulldescription", "fullDescription", "Story", "story", "description"):
            v = item.get(key) or sub.get(key)
            if isinstance(v, str) and v.strip():
                desc_parts.append(v.strip())
        description = "\n\n".join(dict.fromkeys(desc_parts))[:8000]
        ot          = original_title or (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
        title       = (item.get("title") or "").strip()
        script_src  = ot or title
        return {
            "title":        title or None,
            "original_title": ot or None,
            "categoryName": item.get("categoryName") or item.get("categoryText"),
            "publisher":    item.get("publisher"),
            "description":  description or None,
            "script_weights": _script_weights_on_text(script_src),
        }

    @staticmethod
    def _build_author_info(name: str, bio: str) -> Dict[str, Any]:
        """
        GPT payload용 저자 단서 묶음.
        (trans.py build_author_info_for_llm 이식)
        """
        bio_s  = (bio or "").strip()
        name_s = (name or "").strip()
        return {
            "name":           name_s,
            "bio_excerpt":    bio_s[:1000] if bio_s else None,
            "script_weights": _script_weights_on_text(f"{name_s} {bio_s[:2000]}"),
            "univ_major_regex": extract_univ_major_regex(bio_s) if bio_s else None,
        }

    @staticmethod
    def _build_translator_info(
        name: str,
        bio: str,
    ) -> Dict[str, Any]:
        """GPT payload용 역자 단서 묶음 (전공/Bio만 — 커리어 힌트 제거)."""
        bio_s = (bio or "").strip()
        return {
            "name":             (name or "").strip(),
            "bio_excerpt":      bio_s[:1000] if bio_s else None,
            "univ_major_regex": extract_univ_major_regex(bio_s) if bio_s else None,
        }

    # ─────────────────────────────────────────────
    # 2-1c. 비문학 전용 JSON Payload GPT 판정
    # ─────────────────────────────────────────────

    # 시스템 프롬프트 — trans.py determine_origin_country_by_llm 원문 그대로 이식
    # 시스템 프롬프트 — A부터 L까지 논리적 순서로 완벽하게 재정렬 및 보강됨
    _NONFICTION_SYSTEM_PROMPT: str = (
        "당신은 한국어로 번역·출간된 외국 도서의 원서 언어·원서 국가를 추론하는 전문가입니다.\n"
        "입력은 알라딘 번역서 데이터입니다.\n\n"

        "══════════════════════════════════════════════════════\n"
        "## 절대 금지 규칙\n"
        "══════════════════════════════════════════════════════\n\n"

        "### 규칙 A. '국내도서' ≠ 한국어 원서\n"
        "categoryName의 '국내도서'·'국내'·'한국'은 유통 분류일 뿐입니다.\n"
        "절대 금지: '국내도서'만 보고 한국어 원서·한국을 원서 국가로 판정.\n\n"

        "### 규칙 B. 외국인 이름 음차 처리\n"
        "authors[].name이 외국 인명의 한글 음차이면 한국어 원서 판정 절대 금지.\n"
        "  · 전형적 한국 성씨(김·이·박·최·정·강·조·윤·장·임)만 있는 이름이 아니면 외국인으로 간주.\n"
        "  · bio 부재를 이유로 한국어 기본값 금지.\n"
        "  · ★ 예외 — 역자 정보가 없고, 저자 이름이 '루하'·'은유' 등 순한글 2~3글자 필명이면\n"
        "    kor 가능성을 최우선 고려. 역자 없음 + 한글 필명 = kor 또는 und.\n\n"

        "### 규칙 C. 도서 제목의 결정적 고유명사\n"
        "title·description에 특정 국가·문화권 고유명사가 있으면 즉시 판정.\n"
        "  · 일본: 지브리·라퓨타·토토로 등 → jpn\n"
        "  · 미국: 마블·디즈니·픽사·스타워즈 등 → eng\n\n"

        "### 규칙 D. 역자 국적으로 인한 궤변 금지\n"
        "한국인 번역가가 번역했다는 사실은 원서 언어 추론에 무관합니다.\n"
        "  · '역자가 한국인이므로 원서를 단정할 수 없다'는 논리 절대 금지.\n\n"

        "### 규칙 E. '번역 결과 = 원서' 혼동 및 궤변 절대 금지\n"
        "원서 언어($h)는 번역가가 **번역하기 전 원본의 언어**입니다.\n"
        "  · 절대 금지: '역자가 한국어로 번역했으므로 원서는 한국어(kor)다'라는 논리적 오류.\n"
        "  · 절대 금지: '역자가 한국인이므로 한국어(kor)일 수 있다'는 궤변.\n"
        "  · 이 데이터의 모든 책은 한국어로 번역되어 출간된 것입니다.\n"
        "    따라서 '한국어로 번역되었다'는 사실은 원서 언어 추론에 0.1%의 영향도 주지 않습니다.\n"
        "  · 저자의 국적·활동 언어로 외국어(예: 스페인어)로 결론이 났다면,\n"
        "    뒤도 돌아보지 말고 해당 외국어로 즉시 확정하십시오.\n\n"
        "  ★ 금지어 목록 — reasoning_process에 아래 표현이 포함되면 즉시 Failure입니다:\n"
        "    - '한국어로 번역되었으므로'\n"
        "    - '한국어로 번역한 점을 고려하여'\n"
        "    - '한국 시장에 출간되었으니'\n"
        "    - '한국어로 출간된 점'\n"
        "    - '도착어가 한국어이므로'\n"
        "    위 표현들은 원서 언어와 완전히 무관한 정보를 근거로 삼는 것으로, 사용 즉시 탈락합니다.\n\n"
        "  ★ 사족 금지 — 강제 추론 종료 규칙:\n"
        "    reasoning_process에서 외국어 단서를 확인한 순간,\n"
        "    반드시 '따라서 원서 언어는 OO어다.'라고 마침표를 찍고 추론을 즉시 종료하십시오.\n"
        "    그 뒤에 '그러나', '하지만', '단', '다만' 등의 역접 접속사로 이어지는\n"
        "    어떠한 사족도 절대 붙이지 마십시오. 사족이 붙는 순간 탈락입니다.\n\n"

        "### 규칙 F. 고전·종교·역사 텍스트의 원전 언어 우대\n"
        "고대/중세 인물이거나 종교적 맥락이 뚜렷한 경우,\n"
        "'영어판 등을 거친 중역일지 모른다'는 지레짐작으로 'und'를 출력하는 것을 절대 금지합니다.\n"
        "  · 역자가 해당 종교·고전 전공자(예: 정교회 신학원 수학, 철학과, 고전어 전공)라는\n"
        "    단서가 있다면, 역자가 원전을 직접 번역했을 확률이 매우 높습니다.\n"
        "    의심하지 말고 저자의 역사적 원전 언어로 즉시 확정하십시오.\n"
        "  · 종교·문화권별 기본 원전 언어 참고:\n"
        "    - 정교회(동방정교) 교부 저작 → 그리스어(gre)\n"
        "    - 가톨릭 라틴 교부·스콜라철학 → 라틴어(lat)\n"
        "    - 고대 그리스 철학·문학 (플라톤·아리스토텔레스·호메로스 등) → 그리스어(gre)\n"
        "    - 고대 로마 문학·철학 (키케로·베르길리우스·세네카 등) → 라틴어(lat)\n"
        "    - 러시아 정교회 성인 저작 → 러시아어(rus)\n"
        "  · 예: 저자가 성 요한 크리소스토모스(4세기 정교회 교부) + 역자가 정교회 신학원 출신\n"
        "    → 중역 의심 금지 → 그리스어(gre) 즉시 확정\n\n"

        "### 규칙 G. 작자 미상 고전·경전의 저자 부재 페널티 면제\n"
        "바가바드 기타·불경·성서 등 작자가 미상이거나 집단 지성으로 쓰여진 고대 문헌/경전의 경우,\n"
        "'저자 정보가 없다'는 이유로 판별을 포기하고 'und'를 반환하는 것을 절대 금지합니다.\n"
        "  · 도서 메타데이터(제목·고유명사)와 역자 전공(동양 고전·인도 철학·불교학 등)만\n"
        "    일치한다면, 저자 정보 없이도 해당 원전 언어로 즉시 확정하십시오.\n"
        "  · 경전·문헌별 원전 언어 참고:\n"
        "    - 바가바드 기타·우파니샤드·리그베다 등 힌두 경전 → 산스크리트어(san)\n"
        "    - 빨리어 불경(니카야·테라바다 계열) → 팔리어(pal)\n"
        "    - 한역 불경(한자 번역본 원전) → 중국어(chi) 또는 산스크리트어(san)\n"
        "    - 구약성서 원전 → 히브리어(heb) / 신약성서 원전 → 그리스어(gre)\n"
        "    - 쿠란 원전 → 아랍어(ara)\n"
        "  · 예: 제목에 '바가바드 기타' + 역자가 인도 철학 전공\n"
        "    → 저자 정보 없음은 페널티 아님 → 산스크리트어(san) 즉시 확정\n\n"

        "### 규칙 H. 역자 부재 시 기본값 제한\n"
        "역자 정보가 없는 경우 무작정 영어를 기본값으로 출력하는 것을 금지합니다.\n"
        "  · 역자 없음 + 한글 필명 → kor\n"
        "  · 역자 없음 + 외국식 이름 + 추가 단서 없음 → und\n"
        "  · 역자 없음 + 외국식 이름 + bio에 한국 활동 명확 → kor 우선 고려\n"
        "  · 역자 없음 + 외국식 이름이어도 이름만으로 외국어 원서 단정 금지\n"
        "  · 역자 있음 + 단서 부족 → eng 기본값 허용\n\n"
        "  ★★ 핵심 추가 규칙 — 저자의 직업·전공으로 원서 언어 단정 금지:\n"
        "  역자가 없는데 저자가 '영어 전문가', '번역가', '영어 강사', '영어 콘텐츠 개발자' 등\n"
        "  영어 관련 직업을 가지고 있다는 사실은 원서가 영어라는 증거가 절대 아닙니다.\n"
        "  한국인 저자가 영어를 가르치거나 번역하는 사람이라도, 그 저자가 직접 집필한\n"
        "  책의 원서는 한국어일 수 있습니다.\n"
        "  자동 탈락(Failure) 조건:\n"
        "    '저자가 영어 관련 직업이므로 원서는 영어다' → 즉시 탈락\n"
        "    '저자가 번역가이므로 원서는 외국어다' → 즉시 탈락\n"
        "  역자 없음 + 한국인 저자 + 직업이 영어/외국어 관련 → und (원서 언어 판별 불가)\n\n"

        "══════════════════════════════════════════════════════\n"
        "## 종합 추론(Synthesis) 방식\n"
        "══════════════════════════════════════════════════════\n\n"

        "저자 정보와 역자 정보를 **우선순위 없이 동등한 단서**로 취급하십시오.\n"
        "두 단서를 퍼즐 맞추듯 종합(Synthesis)하여 가장 논리적인 원서 언어를 추론하십시오.\n\n"

        "종합 추론 예시:\n"
        "  · 저자가 독일인 + 역자가 독문학 전공 → 두 단서 일치 → 독일어(ger) 확정\n"
        "  · 저자가 일본인 + 역자가 영문학 전공 → 충돌 → 다른 단서(원제·bio) 추가 검토\n"
        "  · 저자 bio 없음 + 역자가 노어노문학과 → 역자 단서로 러시아어(rus) 추론\n"
        "  · 저자 bio에 '파리 태생' + 역자가 불문학 전공 → 프랑스어(fre) 확정\n\n"

        "★ 단서 충돌 시 'und'로 도망가지 마십시오.\n"
        "  충돌할 때는 더 구체적인 단서(전공명, 출생지, 원제 언어 등)를 우선 채택하고\n"
        "  reasoning_process에 충돌 내용과 판단 근거를 반드시 서술하십시오.\n\n"

        "### 규칙 I. 모든 제공 단서의 동등한 반영 및 모순 추론 지침\n"
        "데이터 내에 저자 정보와 역자(translators) 정보가 모두 주어졌을 때,\n"
        "한쪽 정보만 보고 반대쪽 정보를 뇌내망상으로 생략하거나 뭉개는 행위를 절대 금지합니다.\n"
        "  · 특히 저자가 한국인 성명이거나 기독교·설교집 맥락이 강하다는 이유로,\n"
        "    역자 프로필에 명시된 구체적인 단서(예: '일본어 전공')를\n"
        "    누락하거나 무시한 채 무작정 '한국어(kor)'로 결론짓지 마십시오.\n"
        "  · extracted_facts에 나열된 모든 저자·역자의 전공, 활동국, 학위 단서를\n"
        "    빠짐없이 테이블 위에 올려놓고 종합적으로 추론을 전개하십시오.\n\n"

        "### 규칙 J. 거짓 일치(Forced Match) 및 억지 논리 절대 금지\n"
        "저자의 언어 힌트와 역자의 전공 힌트가 명백히 다름에도 불구하고(예: 저자=스웨덴어/영어, 역자=중국어 전공), 결론을 정당화하기 위해 '두 정보가 일치한다'고 거짓 서술하는 할루시네이션을 절대 금지합니다.\n"
        "  · 두 단서가 충돌하면 '일치한다'고 뭉뚱그리지 말고, '역자의 전공(중국어)은 본 도서의 언어(영어)와 무관하므로 저자 단서를 우선 채택한다'와 같이 인과관계를 객관적으로 서술하십시오.\n\n"

        "### 규칙 L. '한국인 저자 + 외국어 역자' 조합의 절대 원칙 [자동 탈락 조건 포함]\n"
        "저자가 한국인이거나 한국에서 활동하는 인물이더라도,\n"
        "역자가 특정 외국어 전공자(예: 일본어 박사, 독문학 전공, 노어노문학과 등)임이 확인된 경우,\n"
        "반드시 아래 논리를 강제 적용하십시오:\n\n"
        "  ★ 강제 추론 프레임:\n"
        "    '이 책은 한국인 저자가 해당 외국어(일본어 등)로 집필했거나,\n"
        "    해외에서 먼저 외국어로 출판된 뒤 한국에 번역 소개된 것이다.'\n\n"
        "  ★ 자동 탈락(Failure) 조건:\n"
        "    역자의 외국어 전공이 확인된 상태에서 저자의 국적·활동지만을 근거로\n"
        "    '저자가 한국인이므로 원서는 한국어(kor)다'라고 결론 내리는 행위는\n"
        "    분석 실패(Failure)로 간주하며 즉시 무효 처리합니다.\n\n"
        "  ★ 핵심 논거:\n"
        "    - 역자가 특정 외국어 전공자라는 사실 자체가, 해당 언어의 원문이\n"
        "      존재한다는 가장 강력한 물리적 증거입니다.\n"
        "    - 저자가 한국인이라는 사실은 '원서 언어 = 한국어'를 지지하는 근거가\n"
        "      절대로 될 수 없습니다. 한국인도 외국어로 집필하거나 해외에서 먼저\n"
        "      출판할 수 있기 때문입니다.\n"
        "    - 역자의 전공 언어 ≠ 저자의 국적 언어일 때, 역자 단서를 우선 채택하고\n"
        "      저자 국적 단서는 원서 언어 판단에서 제외하십시오.\n\n"
        "  ★ 판정 예시:\n"
        "    - 저자: 이해영(한국인) + 역자: 하태후(일본어 박사)\n"
        "      → '저자가 한국인이므로 kor' ← 자동 탈락(Failure)\n"
        "      → '역자가 일본어 전공이므로 원문은 jpn' ← 정답\n"
        "    - 저자: 김민준(한국인) + 역자: 박지현(독문학 전공)\n"
        "      → '저자가 한국인이므로 kor' ← 자동 탈락(Failure)\n"
        "      → '역자가 독문학 전공이므로 원문은 ger' ← 정답\n\n"

        "## author_signal_confidence\n"
        "- high: 저자·역자 단서가 동일 언어를 가리키거나 결정적 단서 존재\n"
        "- medium: 단서가 있으나 일부 불확실\n"
        "- low: 단서 빈약 — 역자 전공·원제 등 간접 단서로 추론\n\n"

        "══════════════════════════════════════════════════════\n"
        "## [최종 경고] 규칙 K. 결론 직전 자가 검증 — 번역 결과 혼동 최종 차단\n"
        "══════════════════════════════════════════════════════\n\n"
        "inferred_language를 출력하기 직전, 반드시 아래를 자가 점검하십시오:\n"
        "  1. 지금 내가 추론한 언어가 '저자의 원서 언어'인가, 아니면 '이 책이 한국에서\n"
        "     한국어로 출간되었다는 사실'에서 비롯된 것인가?\n"
        "  2. 만약 extracted_facts의 author_info·translator_info에서 이미 특정 외국어\n"
        "     (예: 일본어, 독일어 등)로 단서를 명확히 잡았는데도, 결론에서 '역자가\n"
        "     한국어로 번역/출간했으므로 한국어(kor)'라는 식으로 뒤집고 있다면,\n"
        "     이는 100% 할루시네이션입니다. 즉시 그 결론을 폐기하고 앞서 잡은\n"
        "     외국어 단서로 되돌리십시오.\n"
        "  · 저자·역자 단서를 종합해 외국어로 결론이 났다면, 마지막 순간에 동요하지\n"
        "    말고 그 외국어를 inferred_language로 그대로 출력하십시오.\n\n"
        "  ★★★ 절대 금지 — 다음 패턴은 시스템 최고 수준 위반(Critical Failure)입니다 ★★★\n"
        "  추론 과정에서 외국어(티베트어, 스웨덴어, 일본어 등)라고 확신까지 서술해 놓고,\n"
        "  마지막에 '한국어로 번역되었으므로 kor'로 뒤집는 행위.\n\n"
        "  실제 발생한 Critical Failure 예시 (절대 반복 금지):\n"
        "    '저자는 티베트 출신 승려고, 역자는 달라이 라마의 통역사다.\n"
        "     → 티베트어일 가능성이 높다.\n"
        "     그러나 역자가 한국어로 번역한 점을 고려하여 → 한국어(kor) 확정.'\n"
        "  위 추론은 99% 정답을 맞히고 마지막 1%에서 스스로 뒤집은 최악의 오류입니다.\n"
        "  외국어로 결론이 났다면 '그러나', '하지만', '다만' 따위의 역접은 존재할 수 없습니다.\n"
        "  티베트어면 티베트어, 스웨덴어면 스웨덴어, 일본어면 일본어. 그대로 출력하십시오.\n\n"

        "══════════════════════════════════════════════════════\n"
        "## 출력 형식\n"
        "══════════════════════════════════════════════════════\n\n"

        "반드시 JSON 객체 하나만 반환하세요. 키:\n"
        '- extracted_facts (object): 추론에 사용한 팩트를 먼저 정리\n'
        '    · author_info (string): 저자 이름·국적·직업·활동 언어 등 핵심 팩트 요약\n'
        '    · translator_info (string): 역자 전공·학교·번역 이력 등 핵심 팩트 요약. 역자 없으면 "없음"\n'
        '    · book_meta (string): 원제·제목·카테고리 등 도서 메타 단서 요약\n'
        '- reasoning_process (string, 한국어): extracted_facts를 종합한 추론 과정 서술\n'
        '  ★ 작성 규칙: 외국어 단서를 확인한 순간 "따라서 원서 언어는 OO어다."로 마침표를 찍고 종료.\n'
        '    그 이후에 역접("그러나", "하지만", "다만")으로 이어지는 추가 서술 절대 금지.\n'
        '- author_signal_confidence ("high"|"medium"|"low")\n'
        '- inferred_language (string, 한국어 표기: 영어·프랑스어·독일어·노르웨이어 등)\n'
        '  ★ 절대 금지: "판별 불가"·"불명"·"알 수 없음" 등 미판정 표현.\n'
        '  단서 부족 시 기본값:\n'
        '    - 역자 있음 + 단서 부족 → 영어\n'
        '    - 역자 없음 + 한글 필명 → 한국어\n'
        '    - 역자 없음 + 기타 단서 부족 → und\n'
        '- inferred_country (string, 한국어 표기: 미국·프랑스·일본 등)\n'
        '- is_indirect_translation (boolean)\n'
    )


    def gpt_nonfiction_payload(
        self,
        item: Dict,
        original_title: str,
        author_bios: Dict[str, str],   # {저자명: bio} 매핑 dict
        translator_bio: str,
        translator_name: str,
        author_name: str = "",
    ) -> Optional[Dict[str, Any]]:
        """
        비문학 전용 JSON Payload 방식 GPT 판정.
        저자/도서/역자(Bio·전공만) 구조체를 JSON으로 직렬화해 GPT에 전달.
        커리어 힌트(Safe Track)는 제거됨 — 역자 전공(univ_major_regex)만 활용.
        """
        if not self._client:
            return None

        # author_bios가 구버전 str로 넘어온 경우 호환 처리
        if isinstance(author_bios, str):
            author_bios = {"": author_bios}

        sub          = item.get("subInfo") or {}
        authors_list = [a for a in (sub.get("authors") or []) if isinstance(a, dict)]
        writer_names: List[str] = []
        for auth in authors_list:
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _role_is_writer(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    writer_names.append(n)
        if not writer_names and author_name:
            writer_names = [author_name]
        if not writer_names:
            writer_names = _parse_names_from_raw_author(item.get("author") or "", want_translator=False)

        # 저자별 Bio 매핑 — 이름이 일치하면 해당 Bio, 없으면 dict 첫 번째 값 폴백
        def _get_bio_for(name: str) -> str:
            if name in author_bios:
                return author_bios[name]
            # 이름 부분 매칭 (공백·성명 순서 차이 대응)
            for k, v in author_bios.items():
                if k and (k in name or name in k):
                    return v
            # 첫 번째 Bio를 대표 폴백 (단독 저자 케이스)
            return next(iter(author_bios.values()), "") if author_bios else ""

        authors_info    = [self._build_author_info(n, _get_bio_for(n))
                           for n in writer_names[:4]]
        book_info       = self._build_book_info(item, original_title)
        translator_info = self._build_translator_info(translator_name, translator_bio)
        payload = {
            "authors":     authors_info,
            "book":        book_info,
            "translators": [translator_info],
        }

        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": self._NONFICTION_SYSTEM_PROMPT},
                    {"role": "user",
                     "content": json.dumps(payload, ensure_ascii=False, indent=2)},
                ],
                response_format={"type": "json_object"},
                temperature=0,
            )
            raw = (resp.choices[0].message.content or "").strip()
            obj  = json.loads(raw)
            conf = (obj.get("author_signal_confidence") or "low").strip().lower()
            if conf not in ("high", "medium", "low"):
                conf = "low"

            # extracted_facts 수집
            ef = obj.get("extracted_facts") or {}
            extracted_facts = {
                "author_info":     (ef.get("author_info")     or "").strip(),
                "translator_info": (ef.get("translator_info") or "").strip(),
                "book_meta":       (ef.get("book_meta")       or "").strip(),
            }

            result = {
                "extracted_facts":          extracted_facts,
                "reasoning_process":        (obj.get("reasoning_process") or "").strip(),
                "author_signal_confidence": conf,
                "inferred_language":        (obj.get("inferred_language") or "").strip() or "판별 불가",
                "inferred_country":         (obj.get("inferred_country") or "").strip() or "판별 불가",
                "is_indirect_translation":  bool(obj.get("is_indirect_translation")),
                "source": "llm",
            }
            self._dbg(
                f"🧭 [GPT Payload] lang={result['inferred_language']} "
                f"country={result['inferred_country']} "
                f"conf={result['author_signal_confidence']}"
            )
            # extracted_facts 로그 (단서 종합 내용 확인용)
            if extracted_facts.get("author_info"):
                self._dbg(f"🧭 [저자단서] {extracted_facts['author_info'][:80]}")
            if extracted_facts.get("translator_info"):
                self._dbg(f"🧭 [역자단서] {extracted_facts['translator_info'][:80]}")
            if result["reasoning_process"]:
                self._dbg(f"🧭 [추론] {result['reasoning_process'][:200]}")
            return result
        except Exception as e:
            self._dbg_err(f"GPT 오류 (gpt_nonfiction_payload): {e}")
            return None

    @staticmethod
    def detect_language_by_unicode(text: str) -> str:
        """첫 의미 있는 문자의 유니코드 범위로 언어 코드를 반환."""
        text = re.sub(r'[\s\W_]+', '', text or "")
        if not text:
            return 'und'
        c = text[0]
        if '\uac00' <= c <= '\ud7a3': return 'kor'
        if '\u3040' <= c <= '\u30ff': return 'jpn'
        if '\u4e00' <= c <= '\u9fff': return 'chi'
        if '\u0600' <= c <= '\u06FF': return 'ara'
        if '\u0e00' <= c <= '\u0e7f': return 'tha'
        return 'und'

    @staticmethod
    def override_language_by_keywords(text: str, initial_lang: str) -> str:
        """유니코드 감지 결과를 키워드로 보정 (글자/특수문자 단위 추측은 하지 않음)."""
        text = (text or "").lower()
        if initial_lang == 'chi' and re.search(r'[\u3040-\u30ff]', text):
            return 'jpn'
        if initial_lang in ('und', 'eng'):
            if "spanish"    in text or "español"    in text: return "spa"
            if "italian"    in text or "italiano"   in text: return "ita"
            if "french"     in text or "français"   in text: return "fre"
            if "portuguese" in text or "português"  in text: return "por"
            if "german"     in text or "deutsch"    in text: return "ger"
        return initial_lang

    def detect_language(self, text: str) -> str:
        """유니코드 + 키워드 보정으로 언어 감지."""
        lang = self.detect_language_by_unicode(text)
        return self.override_language_by_keywords(text, lang)

    @staticmethod
    def detect_language_from_category(text: str) -> Optional[str]:
        """카테고리 문자열에서 언어 힌트 추출. 없으면 None."""
        words = re.split(r'[>/\s]+', text or "")
        for w in words:
            for keywords, lang in LangFieldBuilder.CATEGORY_LANG_MAP:
                if any(kw in w for kw in keywords):
                    return lang
        return None

    # ─────────────────────────────────────────────
    # 2-3. 카테고리 판정 유틸
    # ─────────────────────────────────────────────

    @staticmethod
    def tokenize_category(text: str) -> list[str]:
        if not text:
            return []
        t = re.sub(r'[()]+', ' ', text)
        raw = re.split(r'[>/\s]+', t)
        tokens: list[str] = []
        for w in raw:
            w = w.strip()
            if not w:
                continue
            if '/' in w and w.count('/') <= 3 and len(w) <= 20:
                tokens.extend(p for p in w.split('/') if p)
            else:
                tokens.append(w)
        lower_tokens = tokens + [
            w.lower() for w in tokens
            if any('A' <= ch <= 'Z' or 'a' <= ch <= 'z' for ch in w)
        ]
        return lower_tokens

    @staticmethod
    def _has_kw(tokens: list[str], kws: list[str]) -> bool:
        s = set(tokens)
        return any(k in s for k in kws)

    @staticmethod
    def _trigger_kw(tokens: list[str], kws: list[str]) -> Optional[str]:
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
        겉보기에는 문학이어도 역사·에세이·사회과학 등 비문학 키워드가
        있으면 비문학으로 강제 처리.
        단, 문학 최상위(소설/시/희곡)이면 SF_GUARD_KEYWORDS(과학/기술)는 제외(SF 보호).
        """
        tokens  = self.tokenize_category(category_text or "")
        lit_top = self.is_literature_top(category_text or "")

        k = (
            self._trigger_kw(tokens, self.NONFICTION_KEYWORDS["ko"])
            or self._trigger_kw(tokens, self.NONFICTION_KEYWORDS["en"])
        )
        if k:
            self._dbg(f"🔎 [판정근거] 비문학 키워드 발견: '{k}'")
            return True

        if not lit_top:
            k2 = (
                self._trigger_kw(tokens, self.SF_GUARD_KEYWORDS["ko"])
                or self._trigger_kw(tokens, self.SF_GUARD_KEYWORDS["en"])
            )
            if k2:
                self._dbg(f"🔎 [판정근거] 비문학 최상위 추정 & '{k2}' → 비문학 오버라이드")
                return True

        if lit_top:
            self._dbg("🔎 [판정근거] 문학 최상위: 과학/기술은 오버라이드 제외(SF 보호)")
        return False

    @staticmethod
    def is_domestic_category(category_text: str) -> bool:
        return "국내도서" in (category_text or "")

    # ─────────────────────────────────────────────
    # 2-4. $h 결정 로직
    # ─────────────────────────────────────────────

    def reconcile_language(
        self,
        candidate: str,
        fallback_hint: Optional[str] = None,
        author_hint:   Optional[str] = None,
        has_translator: bool = False,
    ) -> str:
        """
        후보(candidate), 보조 규칙 힌트(fallback_hint),
        저자 기반 GPT 힌트(author_hint) 세 값을 조정해 최종 반환.
        """
        if author_hint and author_hint != "und" and author_hint != candidate:
            # 역자가 있는데 author_hint가 kor이면 저자 국적만 본 오판 → 무시
            if has_translator and author_hint == "kor":
                self._dbg(f"🔁 [조정] 역자 있음 + author_hint=kor → 오판 차단, 후보({candidate}) 유지")
            else:
                self._dbg(f"🔁 [조정] 저자기반({author_hint}) ≠ 1차({candidate}) → 저자기반 우선")
                return author_hint

        if fallback_hint and fallback_hint != "und" and fallback_hint != candidate:
            if candidate in {"ita", "fre", "spa", "por"} and fallback_hint == "eng":
                # 영어 힌트는 과대검출이 잦음 → GPT 결과 유지
                return candidate
            self._dbg(f"🔁 [조정] 규칙힌트({fallback_hint}) vs 1차({candidate}) → 규칙힌트 우선")
            return fallback_hint

        return candidate

    # ── 파이프라인 단계별 _try_* 메서드 ──────────────

    def _try_rule(
        self,
        subject_lang: str,
        rule_from_original: str,
        label: str = "Rule-based",
    ) -> Optional[str]:
        """
        1단계: 규칙 기반 판정
        subject_lang(크롤링/카테고리 힌트) 또는 원제 유니코드 감지 결과를 반환.
        둘 다 없으면 None.
        """
        result = subject_lang or rule_from_original or None
        if result and result != "und":
            self._dbg(f"📘 [{label}] 규칙 기반 확정: {result}")
            return result
        return None

    def determine_h_language(
        self,
        title: str,
        original_title: str,
        category_text: str,
        publisher: str,
        author: str,
        subject_lang: str,
        item: Optional[dict] = None,  # API item dict 전체 (Bio 수집에 사용)
        has_translator: bool = False, # 역자 존재 여부 (get_kormarc_tags에서 전달)
    ) -> str:
        """
        원서 언어($h) 최종 결정 — 파이프라인 방식.

        문학 파이프라인  : [Rule-based] → [GPT-General] → [Author-Hint]
        비문학 파이프라인: [Bio 크롤링] → [GPT-General(+Bio)] → [Rule-based]
                           → [Author-Hint(+Bio)]

        비문학으로 판정된 경우에만 저자/역자 Bio를 크롤링하여
        GPT 프롬프트에 주입한다(성능 최적화).

        각 단계는 _try_* 메서드로 독립 캡슐화되어 있으며,
        'und'가 아닌 결과가 나오면 즉시 반환(Early Return)한다.
        마지막에 reconcile_language()로 충돌을 조정하고,
        ALLOWED_CODES 검사 후 'und'로 폴백한다.
        """
        lit_raw     = self.is_literature_category(category_text)
        nf_override = self.is_nonfiction_override(category_text)
        is_lit      = lit_raw and not nf_override

        # 판정 결과 설명 로깅
        if lit_raw and not nf_override:
            self._dbg("📘 [판정] 문학(소설/시/희곡 등) 성격이 뚜렷합니다.")
        elif lit_raw and nf_override:
            self._dbg("📘 [판정] 겉보기 문학 + 비문학 요소 → 비문학으로 처리.")
        elif not lit_raw and nf_override:
            self._dbg("📘 [판정] 비문학(역사·사회·철학 등) 성격이 강합니다.")
        else:
            self._dbg("📘 [판정] 문학/비문학 단서 약함 → 추가 판단 진행.")

        # rule_from_original 산출: 원제가 순수 라틴 문자라면 1단계 규칙 기반 감지를
        # 무조건 건너뛰고 'und'를 강제한다.
        # 이유: detect_language() → override_language_by_keywords()가 "german"·"french" 등
        # 언어명 키워드를 단어 경계 없이 부분 문자열로 검사하기 때문에,
        # 'Germania'(라틴어 원제) 같은 단어가 "german"을 포함한다는 이유만으로
        # ger로 오판되어 1.5단계(원제 전용 단어 단위 GPT)가 실행되지 못하는 문제가 있다.
        # 라틴 문자 원제는 전부 1.5단계의 정밀 분석에 위임한다.
        _ot_is_latin_only = (
            bool(original_title)
            and bool(_RE_LATIN.search(original_title))
            and not _RE_NON_LATIN.search(original_title)
        )
        if _ot_is_latin_only:
            rule_from_original = "und"
        else:
            rule_from_original = (
                self.detect_language(original_title)
                if original_title else "und"
            )
        fallback_hint = subject_lang or rule_from_original or None

        # ── 비문학 파이프라인 ─────────────────────────────────
        if not is_lit:
            _item = item or {}

            # ══════════════════════════════════════════════════
            # 1단계: 원제 유니코드 조기 반환 (크롤링·GPT 완전 스킵)
            # ══════════════════════════════════════════════════
            # rule_from_original이 und·eng 가 아니면 즉시 확정
            # (eng 제외: 라틴 문자는 불어·독어 등과 구분 불가)
            if rule_from_original and rule_from_original not in ("und", "eng"):
                self._dbg(
                    f"📘 [1단계/유니코드] 원제 '{original_title}' → "
                    f"{rule_from_original}({ISDS_LANGUAGE_CODES.get(rule_from_original, '?')}) "
                    "즉시 확정 (크롤링·GPT 스킵)"
                )
                return rule_from_original

            self._dbg(
                f"📘 [1단계/유니코드] 원제 '{original_title or '없음'}' → "
                f"rule={rule_from_original} (eng·und → 다음 단계 진행)"
            )

            # ══════════════════════════════════════════════════
            # 1.5단계: 원제 전용 경량 GPT — Bio 크롤링 전 조기 확정 시도
            # ══════════════════════════════════════════════════
            # 조건: 원제가 있고, 라틴 알파벳만으로 이루어진 경우에만 실행.
            # 한자·가나·키릴·아랍 등 비라틴 스크립트가 섞인 원제는 스킵
            # (1단계에서 이미 처리됐거나 2단계 GPT Payload에 위임).

            # ── 1.5단계 전용 노이즈 제거 ───────────────────────
            # 원제에 포함된 괄호 안 연도·한국어 표기(예: '(2000년)', '(개정판)', '(양장본)')를
            # 제거한 사본으로 라틴 문자 여부를 판별하고, GPT에도 이 사본을 전달한다.
            # 원본 original_title은 변경하지 않는다(로그·다른 단계에서 그대로 사용).
            _cleaned_title = re.sub(
                r"\([^)]*[\uAC00-\uD7A3\d][^)]*\)",  # 괄호 안에 한글 또는 숫자 포함 시 제거
                "",
                (original_title or ""),
            ).strip()
            # 남은 빈 괄호·불필요한 공백 정리
            _cleaned_title = re.sub(r"\(\s*\)", "", _cleaned_title).strip()
            _cleaned_title = re.sub(r"\s{2,}", " ", _cleaned_title).strip()

            _is_latin_only = (
                bool(_cleaned_title)
                and _RE_LATIN.search(_cleaned_title)
                and not _RE_NON_LATIN.search(_cleaned_title)
            )
            if _is_latin_only:
                _log_title = (
                    f"'{_cleaned_title}' (원제 노이즈 제거: '{original_title}')"
                    if _cleaned_title != original_title
                    else f"'{original_title}'"
                )
                self._dbg(f"📘 [1.5단계] 라틴 원제 GPT 판별 시작: {_log_title}")
                title_lang = self.gpt_guess_from_original_title_only(_cleaned_title)
                if title_lang and title_lang != "und":
                    self._dbg(
                        f"📘 [1.5단계/원제GPT] '{_cleaned_title}' → "
                        f"{title_lang}({ISDS_LANGUAGE_CODES.get(title_lang, '?')}) "
                        "확정 — Bio 크롤링·GPT Payload 스킵"
                    )
                    return title_lang
                self._dbg(
                    "📘 [1.5단계/원제GPT] 판단 보류(und) → 2단계(Bio+GPT Payload)로 진행"
                )
            elif original_title:
                self._dbg(
                    f"📘 [1.5단계] 원제 '{original_title}' — "
                    "비라틴 문자 포함(노이즈 제거 후에도) → 스킵, 2단계로 진행"
                )
            else:
                self._dbg("📘 [1.5단계] 원제 없음 → 스킵, 2단계로 진행")

            # ══════════════════════════════════════════════════
            # 2단계: 저자/역자 Bio 크롤링 → GPT 단일 호출
            # ══════════════════════════════════════════════════
            author_bios: Dict[str, str] = {}
            translator_bio = ""
            self._dbg("📘 [2단계] Bio 수집 시작…")
            try:
                author_bios, translator_bio = self._scraper.fetch_bios(_item)
                if author_bios:
                    self._dbg(f"📘 [Bio] 저자 Bio {len(author_bios)}명 수집")
                    for _n, _b in author_bios.items():
                        if _b:
                            self._dbg(f"📘 [Bio]   · {_n}: {len(_b)}자")
                if translator_bio:
                    self._dbg(f"📘 [Bio] 역자 Bio {len(translator_bio)}자")
                if not author_bios and not translator_bio:
                    self._dbg("📘 [Bio] Bio 없음")
            except Exception as e:
                self._dbg_err(f"Bio 수집 오류: {e}")

            # 역자 이름 추출 (Payload 전달용)
            tr_names: List[str] = []
            sub_info = _item.get("subInfo") or {}
            for auth in (sub_info.get("authors") or []):
                if isinstance(auth, dict) and _role_is_translator(
                    (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "")
                ):
                    n = (auth.get("authorName") or "").strip()
                    if n:
                        tr_names.append(n)
            if not tr_names:
                tr_names = _parse_names_from_raw_author(
                    _item.get("author") or "", want_translator=True
                )
            translator_name_for_payload = tr_names[0] if tr_names else ""

            # GPT 단일 호출 (커리어 힌트 없이)
            self._dbg("📘 [2단계] GPT Payload 판정…")
            # 저자 이름 추출 (Payload author_name 전달용)
            _author_names_for_payload = _parse_names_from_raw_author(
                _item.get("author") or "", want_translator=False
            )
            _author_name_for_payload = _author_names_for_payload[0] if _author_names_for_payload else ""

            llm_result = self.gpt_nonfiction_payload(
                item=_item,
                original_title=original_title,
                author_bios=author_bios,
                translator_bio=translator_bio,
                translator_name=translator_name_for_payload,
                author_name=_author_name_for_payload,
            )

            if llm_result:
                lang_name = llm_result.get("inferred_language", "")

                # ★ 역자 존재 + GPT가 한국어로 판정 = 할루시네이션 차단
                if has_translator and lang_name.strip().lower() in ("kor", "korean", "한국어"):
                    self._dbg(
                        f"📘 [2단계/GPT] ⚠️ 역자 존재 + 'kor' 판정 → 할루시네이션 의심, "
                        f"무효화하여 und 처리 (원본 추론: '{lang_name}')"
                    )
                    lang_name = "und"

                # ★ 역자 없음 + 외국어 판정 = 할루시네이션 차단 (규칙 H 코드 레벨 보완)
                # 역자가 없는 책을 외국어 원서로 판정하는 것은 오판.
                # 저자의 직업(영어 강사, 번역가 등)을 근거로 영어를 판정하는 경우가 대표적.
                # → und로 무효화하여 3단계 규칙 폴백으로 넘긴다.
                if not has_translator:
                    _ln_lower = lang_name.strip().lower()
                    _is_foreign = _ln_lower not in ("kor", "korean", "한국어", "und", "")
                    if _is_foreign:
                        self._dbg(
                            f"📘 [2단계/GPT] ⚠️ 역자 없음 + 외국어 판정('{lang_name}') → "
                            "규칙 H 위반 의심, und 처리"
                        )
                        lang_name = "und"

                isds = _resolve_lang_name_to_isds(lang_name) if lang_name else None
                if isds and isds in ALLOWED_CODES:
                    self._dbg(f"📘 [2단계/GPT] 확정: {lang_name} → {isds}")
                    return isds
                self._dbg(f"📘 [2단계/GPT] 미확정 (inferred_language='{lang_name}')")

            # ══════════════════════════════════════════════════
            # 2-b단계: GPT 내부 지식 보완 추론
            # Bio 수집은 됐지만 소개글에서 국적 단서를 못 찾은 경우,
            # GPT가 저자 이름에 대해 알고 있는 정보로 2차 추론 시도.
            # 모르는 저자면 und 반환 → 3단계 규칙 폴백으로 진행.
            # ══════════════════════════════════════════════════
            self._dbg("📘 [2-b단계] GPT 내부 지식 기반 보완 추론 시작…")
            knowledge_result = self.gpt_guess_by_author_knowledge(
                author_name=_author_name_for_payload,
                translator_name=translator_name_for_payload,
                has_translator=has_translator,
                title=title,
                original_title=original_title,
            )
            if knowledge_result and knowledge_result != "und":
                self._dbg(f"📘 [2-b단계] 지식 추론 확정: {knowledge_result}")
                return knowledge_result
            self._dbg("📘 [2-b단계] 지식 추론 미확정 → 3단계로 진행")

            # ══════════════════════════════════════════════════
            # 3단계: 규칙 기반 폴백
            # ══════════════════════════════════════════════════
            rule_result = self._try_rule(subject_lang, rule_from_original, "Rule-based(폴백)")
            if rule_result:
                self._dbg(f"📘 [3단계/Rule] 확정: {rule_result}")
                return rule_result

            self._dbg("📘 [비문학] 전 단계 미확정 → und")
            return "und"

        # ── 문학 파이프라인 ───────────────────────────────────
        self._dbg("📘 [Pipeline] 문학: 카테고리 확인 → Rule-based → Bio크롤링+GPT Payload")

        # ══════════════════════════════════════════════════
        # Step 0: 카테고리에서 명시적 언어(예: '독일소설' → ger)가 감지되면
        # 즉시 반환하여 이후 크롤링·GPT 호출을 완전히 스킵한다.
        # ══════════════════════════════════════════════════
        self._dbg(f"📘 [Step0] 카테고리 텍스트: '{category_text}'")
        cat_lang_hint = self.detect_language_from_category(category_text)
        if cat_lang_hint:
            self._dbg(
                f"📘 [Step0/Category] 카테고리에서 '{cat_lang_hint}' 감지 → "
                "즉시 확정 (크롤링·GPT 스킵)"
            )
            return cat_lang_hint

        # ══════════════════════════════════════════════════
        # Step 1: 규칙 기반 1차 시도 (subject_lang 힌트 또는 원제 유니코드 감지)
        # ══════════════════════════════════════════════════
        rule_result = self._try_rule(subject_lang, rule_from_original, "Rule-based")
        if rule_result:
            self._dbg(f"📘 [Step1/Rule] 확정: {rule_result}")
            lang_h = self.reconcile_language(
                candidate=rule_result,
                fallback_hint=fallback_hint,
                author_hint=None,
                has_translator=has_translator,
            )
            self._dbg(f"📘 [결과] 조정 후 원서 언어(h) = {lang_h}")
            return lang_h if lang_h in ALLOWED_CODES else "und"

        # ══════════════════════════════════════════════════
        # Step 2: 저자/역자 Bio 크롤링 → GPT Payload 단일 호출
        # (비문학 2단계와 완전히 동일한 구조로 업그레이드)
        # ══════════════════════════════════════════════════
        _item = item or {}
        author_bios: Dict[str, str] = {}
        translator_bio = ""
        self._dbg("📘 [Step2] Bio 수집 시작…")
        try:
            author_bios, translator_bio = self._scraper.fetch_bios(_item)
            if author_bios:
                self._dbg(f"📘 [Bio] 저자 Bio {len(author_bios)}명 수집")
            if translator_bio:
                self._dbg(f"📘 [Bio] 역자 Bio {len(translator_bio)}자")
            if not author_bios and not translator_bio:
                self._dbg("📘 [Bio] Bio 없음")
        except Exception as e:
            self._dbg_err(f"Bio 수집 오류: {e}")

        # 역자 이름 추출 (Payload 전달용)
        tr_names: List[str] = []
        sub_info = _item.get("subInfo") or {}
        for auth in (sub_info.get("authors") or []):
            if isinstance(auth, dict) and _role_is_translator(
                (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "")
            ):
                n = (auth.get("authorName") or "").strip()
                if n:
                    tr_names.append(n)
        if not tr_names:
            tr_names = _parse_names_from_raw_author(
                _item.get("author") or "", want_translator=True
            )
        translator_name_for_payload = tr_names[0] if tr_names else ""

        # 저자 이름 추출 (Payload author_name 전달용)
        _author_names_for_payload = _parse_names_from_raw_author(
            _item.get("author") or "", want_translator=False
        )
        _author_name_for_payload = _author_names_for_payload[0] if _author_names_for_payload else ""

        self._dbg("📘 [Step2] GPT Payload 판정…")
        llm_result = self.gpt_nonfiction_payload(
            item=_item,
            original_title=original_title,
            author_bios=author_bios,
            translator_bio=translator_bio,
            translator_name=translator_name_for_payload,
            author_name=_author_name_for_payload,
        )

        author_hint: Optional[str] = None
        if llm_result:
            lang_name = llm_result.get("inferred_language", "")

            # ★ 역자 존재 + GPT가 한국어로 판정 = 할루시네이션 차단 (비문학과 동일 가드)
            # 역자가 있다는 것은 번역서라는 뜻이고, 번역서의 원서가 한국어일 수는
            # 없다(중역이 아닌 한). GPT가 역자의 국적·경력만 보고 'kor'로 오판하는
            # 경우를 무효화하여 충돌 조정 단계로 안전하게 넘긴다.
            if has_translator and lang_name.strip().lower() in ("kor", "korean", "한국어"):
                self._dbg(
                    f"📘 [Step2/GPT] ⚠️ 역자 존재 + 'kor' 판정 → 할루시네이션 의심, "
                    f"무효화하여 und 처리 (원본 추론: '{lang_name}')"
                )
                lang_name = "und"

            isds = _resolve_lang_name_to_isds(lang_name) if lang_name else None
            if isds and isds in ALLOWED_CODES:
                self._dbg(f"📘 [Step2/GPT] 확정: {lang_name} → {isds}")
                author_hint = isds
            else:
                self._dbg(f"📘 [Step2/GPT] 미확정 (inferred_language='{lang_name}')")

        # ── Step 2-b: GPT 내부 지식 보완 추론 ─────────────────
        # Step2가 미확정인 경우, 저자 이름에 대한 GPT 사전 지식으로 2차 시도.
        if not author_hint:
            self._dbg("📘 [Step2-b] GPT 내부 지식 기반 보완 추론 시작…")
            knowledge_result = self.gpt_guess_by_author_knowledge(
                author_name=_author_name_for_payload,
                translator_name=translator_name_for_payload,
                has_translator=has_translator,
                title=title,
                original_title=original_title,
            )
            if knowledge_result and knowledge_result != "und":
                self._dbg(f"📘 [Step2-b] 지식 추론 확정: {knowledge_result}")
                author_hint = knowledge_result
            else:
                self._dbg("📘 [Step2-b] 지식 추론 미확정 → 충돌 조정으로 진행")

        # ── 충돌 조정 ─────────────────────────────────────────
        lang_h = self.reconcile_language(
            candidate=author_hint or "und",
            fallback_hint=fallback_hint,
            author_hint=author_hint,
            has_translator=has_translator,
        )
        self._dbg(f"📘 [결과] 조정 후 원서 언어(h) = {lang_h}")
        return lang_h if lang_h in ALLOWED_CODES else "und"

    # ─────────────────────────────────────────────
    # 2-5. 최종 KORMARC 태그 생성 (메인 진입점)
    # ─────────────────────────────────────────────

    def get_kormarc_tags(
        self,
        item: dict,
        detail: dict,
    ) -> tuple[Optional[str], Optional[str], str]:
        """
        알라딘 API dict(item)와 크롤링 dict(detail)로부터
        041 · 546 필드 문자열과 원제를 반환.

        Returns
        -------
        (tag_041, tag_546, original_title)
          - 번역서가 아닌 경우  : (None, None, original_title)
          - 번역서인 경우       : ("041 $a... $h...", "546 텍스트", original_title)
          - 예외 발생 시        : ("📕 예외 발생: …", "", original_title)
        """
        item   = item   or {}
        detail = detail or {}

        title     = item.get("title",     "") or ""
        publisher = item.get("publisher", "") or ""
        author    = item.get("author",    "") or ""

        # 원서명 — API subInfo 우선, 없으면 크롤링
        subinfo        = (item.get("subInfo") or {}) or {}
        original_title = html.unescape(subinfo.get("originalTitle", "") or "")
        if not original_title:
            original_title = detail.get("original_title", "") or ""

        subject_lang  = detail.get("subject_lang")
        category_text = (
            item.get("categoryText", "")
            or detail.get("category_text", "")
            or ""
        )

        try:
            # ── $a: 본문 언어 ──────────────────────────────────
            lang_a = self.detect_language(title)
            self._dbg("📘 [DEBUG] 규칙 기반 1차 lang_a =", lang_a)

            # 강한 가드: '국내도서'면 kor 고정
            # 단, 외국어·어학 수험서 카테고리는 예외 — 다중 언어 혼용 가능성
            _is_lang_learning = any(
                kw in (category_text or "")
                for kw in ("외국어", "수험서>어학", "수험서/자격증>어학", "토익", "토플", "JLPT", "HSK")
            )
            if self.is_domestic_category(category_text) and not _is_lang_learning:
                self._dbg("📘 [판정] '국내도서' 감지 → $a=kor 강제")
                lang_a = "kor"
            elif self.is_domestic_category(category_text) and _is_lang_learning:
                self._dbg("📘 [판정] '국내도서>외국어/어학수험서' 감지 → GPT 다중 언어 판정으로 위임")
                lang_a = "und"  # GPT 판정으로 강제 위임

            # GPT 보조: und/eng일 때만 호출 (description도 전달)
            _desc_for_gpt = (
                (item.get("fullDescription") or item.get("description") or "")[:800]
                if isinstance(item, dict) else ""
            )
            _author_for_gpt = item.get("author", "") if isinstance(item, dict) else ""

            # 제목에서 비라틴 문자 사전 감지 → GPT에 힌트로 전달
            import re as _re
            _title_lang_hint = ""
            if _re.search(r'[\u3040-\u30ff]', title):   # 가나 → 일본어
                _title_lang_hint = "※ 제목에 일본어(가나) 문자가 포함되어 있습니다. 본문은 jpn일 가능성이 매우 높습니다."
            elif _re.search(r'[\u4e00-\u9fff]', title) and not _re.search(r'[\u3040-\u30ff]', title):
                _title_lang_hint = "※ 제목에 한자가 포함되어 있습니다. 본문은 chi 또는 jpn일 가능성이 있습니다."
            if _title_lang_hint:
                _desc_for_gpt = _title_lang_hint + "\n\n" + _desc_for_gpt
                self._dbg(f"📘 [본문언어] 제목 비라틴 감지: {_title_lang_hint[:40]}")

            if lang_a in ("und", "eng"):
                self._dbg("📘 [설명] und/eng → GPT 본문 언어 재판정…")
                gpt_a = self.gpt_guess_main_lang(
                    title, category_text, publisher,
                    description=_desc_for_gpt,
                    author_info=_author_for_gpt,
                )
                self._dbg(f"📘 [설명] GPT lang_a = {gpt_a}")
                # 다중 언어("jpn, kor") 그대로 허용 — 쉼표 분리 후 첫 코드만 검증
                _first = gpt_a.split(",")[0].strip() if gpt_a else "und"
                lang_a = gpt_a if _first in ALLOWED_CODES else "und"

            # ── 역자 존재 여부 사전 감지 ───────────────────────
            has_translator = _has_translator_in_item(item)
            if has_translator:
                self._dbg("📘 [번역서감지] 역자(옮긴이) 존재 확인 → $h 판정 필수")

            self._dbg(
                "📘 [DEBUG] 원제 감지됨:", bool(original_title),
                "| 원제:", original_title or "(없음)",
            )
            self._dbg("📘 [DEBUG] 카테고리/크롤링 lang_h 후보 =", subject_lang or "(없음)")

            lang_h = self.determine_h_language(
                title=title,
                original_title=original_title,
                category_text=category_text,
                publisher=publisher,
                author=author,
                subject_lang=subject_lang or "",
                item=item,
                has_translator=has_translator,
            )
            self._dbg("📘 [결과] 최종 원서 언어(h) =", lang_h)

            # ── 최종 태그 조합 ──────────────────────────────────────
            if has_translator and lang_h == lang_a and lang_h != "und":
                self._dbg(f"📘 [보정] 역자 있음 + lang_h({lang_h})==lang_a({lang_a}) → und 처리")
                lang_h = "und"

            has_h = bool(lang_h and lang_h != "und" and lang_h != lang_a)

            # 다중 언어 lang_a("jpn, kor") → $ajpn$akor 형태로 조립
            _a_codes = [c.strip() for c in (lang_a or "").split(",") if c.strip() in ALLOWED_CODES]
            if not _a_codes:
                _a_codes = [lang_a] if lang_a and lang_a != "und" else []
            _a_part = "".join(f"$a{c}" for c in _a_codes) if _a_codes else f"$a{lang_a}"

            if has_h:
                tag_041 = f"041 {_a_part} $h{lang_h}"
            else:
                tag_041 = f"041 {_a_part}"

            # 비번역서($h 없음 + 역자 없음) → 041/546 모두 불필요
            if not has_h and not has_translator:
                return None, None, original_title

            # 번역서인데 $h 판정 실패 → 041($a만)은 유지, 546은 생성 불가
            if not has_h and has_translator:
                self._dbg(
                    "⚠️ [경고] 역자가 있으나 원서 언어($h) 판정 실패 "
                    f"→ tag_041({tag_041}) 유지, tag_546=None 반환"
                )
                return tag_041, None, original_title

            # 정상 번역서: $h 확정 → 041 + 546 모두 생성
            tag_546 = self.generate_546_from_041(tag_041)
            return tag_041, tag_546, original_title

        except Exception as e:
            self._dbg(f"📕 [ERROR] get_kormarc_tags 예외: {e}")
            return f"📕 예외 발생: {e}", "", original_title

    # ─────────────────────────────────────────────
    # 2-6. 546 텍스트 생성
    # ─────────────────────────────────────────────

    @staticmethod
    def generate_546_from_041(marc_041: str) -> str:
        """
        "041 $akor $hrus"           → "러시아어 원작을 한국어로 번역"
        "041 $ajpn$akor $hfre"      → "프랑스어 원작을 일본어와 한국어로 번역"
        "041 $akor"                  → "한국어로 씀"
        "041 $ajpn$akor"             → "일본어, 한국어 병기"
        """
        a_codes: list[str] = []
        h_code:  Optional[str] = None

        # "$ajpn$akor" 와 "$ajpn $akor" 두 형태 모두 지원
        # 먼저 공백 기준으로 토큰 분리 후, 각 토큰 내 $a 반복 패턴 처리
        for token in marc_041.split():
            if token.startswith("$h"):
                h_code = token[2:]
            else:
                # 하나의 토큰에 $a가 여러 개 붙어있을 수 있음 (예: $ajpn$akor)
                for m in re.finditer(r'\$a([a-z]{3})', token):
                    a_codes.append(m.group(1))

        def _lang_name(code: str) -> str:
            return ISDS_LANGUAGE_CODES.get(code, "알 수 없음")

        h_lang = _lang_name(h_code) if h_code else None

        if not a_codes:
            return "언어 정보 없음"

        if len(a_codes) == 1:
            a_lang = _lang_name(a_codes[0])
            if h_lang:
                return f"{h_lang} 원작을 {a_lang}로 번역"
            return f"{a_lang}로 씀"

        # $a가 2개 이상 — 중역 또는 대역
        a_langs = [_lang_name(c) for c in a_codes]
        if h_lang:
            # "프랑스어 원작을 일본어와 한국어로 번역"
            if len(a_langs) == 2:
                return f"{h_lang} 원작을 {a_langs[0]}와 {a_langs[1]}로 번역"
            joined = ", ".join(a_langs[:-1]) + "와 " + a_langs[-1]
            return f"{h_lang} 원작을 {joined}로 번역"
        else:
            # $h 없음 — 대역/병기
            return f"{'·'.join(a_langs)} 병기"

    # ─────────────────────────────────────────────
    # 2-7. MRK 포맷 변환
    # ─────────────────────────────────────────────

    @staticmethod
    def as_mrk_041(tag_041: Optional[str]) -> Optional[str]:
        """
        "041 $akor$hrus"  →  "=041  1\\$akor$hrus"

        - 앞의 '041' / '=041' 제거 후 정규화
        - $a로 시작하지 않으면 None 반환
        """
        if not tag_041:
            return None
        s = tag_041.strip()
        s = re.sub(r"^=?\s*041\s*", "", s)
        s = re.sub(r"\s+", "", s)
        if not s.startswith("$a"):
            return None
        return f"=041  1\\{s}"

    @staticmethod
    def as_mrk_546(tag_546_text: Optional[str]) -> Optional[str]:
        """
        "러시아어 원작을 한국어로 번역"  →  "=546  \\\\$a러시아어 원작을 한국어로 번역"
        (이미 '=546'로 시작하면 그대로)
        """
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

    # ─────────────────────────────────────────────
    # 2-8. 헬퍼
    # ─────────────────────────────────────────────

    @staticmethod
    def extract_lang_h(tag_041_text: Optional[str]) -> Optional[str]:
        """041 태그 문자열에서 $h 코드만 추출. 없으면 None."""
        if not tag_041_text:
            return None
        m = re.search(r"\$h([a-z]{3})", tag_041_text, re.IGNORECASE)
        return m.group(1).lower() if m else None

    @staticmethod
    def lang3_from_tag041(tag_041: Optional[str]) -> Optional[str]:
        """041 태그 문자열에서 $a 코드(008 lang3 override용)만 추출. 없으면 None."""
        if not tag_041:
            return None
        m = re.search(r"\$a([a-z]{3})", tag_041, flags=re.I)
        return m.group(1).lower() if m else None


# ═══════════════════════════════════════════════════════════════
# 3. 모듈 레벨 순수 함수 (하위 호환 / 단독 사용 가능)
# ═══════════════════════════════════════════════════════════════

def _has_translator_in_item(item: dict) -> bool:
    """item dict에 역자(옮긴이)가 존재하는지 확인."""
    sub = (item or {}).get("subInfo") or {}
    for auth in sub.get("authors") or []:
        if not isinstance(auth, dict):
            continue
        role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
        if _role_is_translator(role):
            return True
    raw = (item or {}).get("author") or ""
    return bool(re.search(r"옮긴이|역자|옮김|번역", raw))


def _extract_code_and_reason(
    content: str,
    code_key: str = "$h",
) -> tuple[str, str, str]:
    """GPT 응답을 파싱해 (code, reason, signals) 튜플 반환.
    다중 언어 코드($a=[jpn, kor])의 대괄호도 자동으로 제거한다."""
    code = reason = signals = ""
    for ln in [l.strip() for l in (content or "").splitlines() if l.strip()]:
        if ln.startswith(f"{code_key}="):
            raw = ln.split("=", 1)[1].strip()
            # 대괄호 제거: "[jpn, kor]" → "jpn, kor"
            code = raw.strip("[]").strip()
        elif ln.lower().startswith("#reason="):
            reason = ln.split("=", 1)[1].strip().strip("[]")
        elif ln.lower().startswith("#signals="):
            signals = ln.split("=", 1)[1].strip().strip("[]")
    return code or "und", reason, signals
