"""
lang_field.py
─────────────────────────────────────────────────────────────────────────────
KORMARC 041(언어코드) · 546(언어주기) 필드 생성 모듈

【포함 기능】
  - ISDS 언어코드 상수 / 허용코드 집합
  - GPT 기반 언어 판정   : gpt_guess_original_lang()
                           gpt_guess_main_lang()
                           gpt_guess_original_lang_by_author()
  - 규칙 기반 언어 감지  : detect_language_by_unicode()
                           override_language_by_keywords()
                           detect_language()
                           detect_language_from_category()
  - 카테고리 판정 유틸   : tokenize_category(), is_literature_category(),
                           is_nonfiction_override(), is_domestic_category()
  - $h 결정 로직         : determine_h_language()
                           _try_rule(), _try_gpt_general(), _try_gpt_author()
  - 충돌 조정            : reconcile_language()
  - 최종 KORMARC 태그    : get_kormarc_tags()          → (tag_041, tag_546, orig_title)
  - 546 텍스트 생성       : generate_546_from_041_kormarc()
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
import time
import urllib.parse
from collections import defaultdict
from typing import Callable, Optional

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
    'und': '알 수 없음',
}

ALLOWED_CODES: frozenset[str] = frozenset(ISDS_LANGUAGE_CODES.keys()) - {"und"}


# ═══════════════════════════════════════════════════════════════
# 2. AladinAuthorScraper  — API-First + 웹 크롤링 폴백
# ═══════════════════════════════════════════════════════════════

# ── 역할 판별 상수 ───────────────────────────────────────────────
_TRANSLATOR_ROLE_STRICT: tuple[str, ...] = ("옮긴이", "역자", "옮김", "번역")
_WRITER_ROLE_KEYS:       tuple[str, ...] = ("지은이", "지음", "글")

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

    _WPRODUCT_BASE = "https://www.aladin.co.kr/shop/wproduct.aspx"
    _OVERVIEW_BASE = "https://www.aladin.co.kr/author/wauthor_overview.aspx"
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

    def fetch_bios(self, item: dict) -> tuple[str, str]:
        """
        API-First 방식으로 저자·역자 Bio를 수집.

        Parameters
        ----------
        item : 알라딘 API ItemLookUp 응답의 item dict
               (subInfo.authors, author, fulldescription 등 포함)

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

        author_bio     = self._fetch_single_bio(item, writer_names,     want_translator=False)
        translator_bio = self._fetch_single_bio(item, translator_names, want_translator=True)
        return author_bio, translator_bio

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
        for name in names[:2]:
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

    # 유니코드 특수문자 → 언어 보정 매핑 (override_language_by_keywords용)
    CHAR_LANG_MAP: list[tuple[str, str]] = [
        ("éèêàçùôâîû", "fre"),
        ("ñáíóú",       "spa"),
        ("ãõ",          "por"),
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

    def gpt_guess_original_lang(
        self,
        title: str,
        category: str,
        publisher: str,
        author: str = "",
        original_title: str = "",
        author_bio: str = "",
        translator_bio: str = "",
    ) -> str:
        """원서 언어($h) 추정. 불확실하면 'und'."""
        if not self._client:
            return "und"

        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"

        prompt = f"""
아래 도서의 원서 언어(041 $h)를 ISDS 코드로 추정해줘.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

도서정보:
- 제목: {title}
- 원제: {original_title or "(없음)"}
- 분류: {category}
- 출판사: {publisher}
- 저자: {author}{bio_block}

지침:
- 국가/지역을 언어로 곧바로 치환하지 말 것.
- 저자 국적·주 집필 언어·최초 출간 언어를 우선 고려.
- 저자/역자 소개글이 제공된 경우 국적·활동국·집필 언어 단서를 우선 활용.
- 불확실하면 임의 추정 대신 'und' 사용.

출력형식(정확히 이 2~3줄):
$h=[ISDS 코드]
#reason=[짧게 근거 요약]
#signals=[잡은 단서들, 콤마로](선택)
""".strip()

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
            code, reason, signals = _extract_code_and_reason(content, "$h")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"🧭 [GPT 원서언어] $h={code}")
            if reason:  self._dbg(f"🧭 [이유] {reason}")
            if signals: self._dbg(f"🧭 [단서] {signals}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류 (gpt_guess_original_lang): {e}")
            return "und"

    def gpt_guess_main_lang(
        self,
        title: str,
        category: str,
        publisher: str,
    ) -> str:
        """본문 언어($a) 추정. 불확실하면 'und'."""
        if not self._client:
            return "und"

        prompt = f"""
아래 도서의 본문 언어(041 $a)를 ISDS 코드로 추정.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

입력:
- 제목: {title}
- 분류: {category}
- 출판사: {publisher}

지침:
- '본문 언어'는 이 자료의 현시본(Manifestation) 언어다.
- 저자 국적, 원작 언어, 시리즈 원산지 등 원작 관련 단서 사용 금지.
- 카테고리에 '국내도서'가 있거나, 제목에 한글이 1자라도 포함되면 반드시 kor.
- 허용 코드 밖이거나 불확실하면 'und'.

출력형식:
$a=[ISDS 코드]
#reason=[짧게 근거 요약]
#signals=[잡은 단서들, 콤마로](선택)
""".strip()

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
            code, reason, signals = _extract_code_and_reason(content, "$a")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"🧭 [GPT 본문언어] $a={code}")
            if reason:  self._dbg(f"🧭 [이유] {reason}")
            if signals: self._dbg(f"🧭 [단서] {signals}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류 (gpt_guess_main_lang): {e}")
            return "und"

    def gpt_guess_original_lang_by_author(
        self,
        author: str,
        title: str = "",
        category: str = "",
        publisher: str = "",
        author_bio: str = "",
        translator_bio: str = "",
    ) -> str:
        """저자 정보 기반 원서 언어($h) 추정. 불확실하면 'und'."""
        if not self._client:
            return "und"

        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"

        prompt = f"""
저자 정보를 중심으로 원서 언어(041 $h)를 ISDS 코드로 추정.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

입력:
- 저자: {author}
- (참고) 제목: {title}
- (참고) 분류: {category}
- (참고) 출판사: {publisher}{bio_block}

지침:
- 저자 국적·주 집필 언어·대표 작품 원어를 우선.
- 저자/역자 소개글이 제공된 경우 국적·활동국·집필 언어 단서를 최우선 활용.
- 국가=언어 단순 치환 금지.
- 불확실하면 'und'.

출력형식:
$h=[ISDS 코드]
#reason=[짧게 근거 요약]
#signals=[잡은 단서들, 콤마로](선택)
""".strip()

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
            code, reason, signals = _extract_code_and_reason(content, "$h")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"🧭 [GPT 저자기반] $h={code}")
            if reason:  self._dbg(f"🧭 [이유] {reason}")
            if signals: self._dbg(f"🧭 [단서] {signals}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류 (gpt_guess_original_lang_by_author): {e}")
            return "und"

    # ─────────────────────────────────────────────
    # 2-2. 규칙 기반 감지
    # ─────────────────────────────────────────────

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
        """유니코드 감지 결과를 키워드/특수문자로 보정."""
        text = (text or "").lower()
        if initial_lang == 'chi' and re.search(r'[\u3040-\u30ff]', text):
            return 'jpn'
        if initial_lang in ('und', 'eng'):
            if "spanish"    in text or "español"    in text: return "spa"
            if "italian"    in text or "italiano"   in text: return "ita"
            if "french"     in text or "français"   in text: return "fre"
            if "portuguese" in text or "português"  in text: return "por"
            if "german"     in text or "deutsch"    in text: return "ger"
            # CHAR_LANG_MAP 기반 특수문자 보정
            for chars, lang in LangFieldBuilder.CHAR_LANG_MAP:
                if any(ch in text for ch in chars):
                    return lang
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
    ) -> str:
        """
        후보(candidate), 보조 규칙 힌트(fallback_hint),
        저자 기반 GPT 힌트(author_hint) 세 값을 조정해 최종 반환.
        """
        if author_hint and author_hint != "und" and author_hint != candidate:
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

    def _try_gpt_general(
        self,
        title: str,
        category_text: str,
        publisher: str,
        author: str,
        original_title: str,
        author_bio: str = "",
        translator_bio: str = "",
        label: str = "GPT-General",
    ) -> Optional[str]:
        """
        2단계: GPT 일반 판정 (제목·카테고리·출판사·저자·원제 종합)
        결과가 ALLOWED_CODES에 없으면 None 반환.
        """
        code = self.gpt_guess_original_lang(
            title, category_text, publisher, author, original_title,
            author_bio=author_bio, translator_bio=translator_bio,
        )
        if code and code != "und" and code in ALLOWED_CODES:
            self._dbg(f"📘 [{label}] GPT 일반 판정 확정: {code}")
            return code
        self._dbg(f"📘 [{label}] GPT 일반 판정 미확정 (결과: {code or 'und'})")
        return None

    def _try_gpt_author(
        self,
        author: str,
        title: str,
        category_text: str,
        publisher: str,
        author_bio: str = "",
        translator_bio: str = "",
        label: str = "Author-Hint",
    ) -> Optional[str]:
        """
        3단계: 저자 기반 GPT 판정
        결과가 ALLOWED_CODES에 없으면 None 반환.
        """
        if not author:
            return None
        code = self.gpt_guess_original_lang_by_author(
            author, title, category_text, publisher,
            author_bio=author_bio, translator_bio=translator_bio,
        )
        if code and code != "und" and code in ALLOWED_CODES:
            self._dbg(f"📘 [{label}] 저자 기반 GPT 확정: {code}")
            return code
        self._dbg(f"📘 [{label}] 저자 기반 GPT 미확정 (결과: {code or 'und'})")
        return None

    def determine_h_language(
        self,
        title: str,
        original_title: str,
        category_text: str,
        publisher: str,
        author: str,
        subject_lang: str,
        item_id: str = "",       # 하위 호환용 (사용 안 함)
        item: Optional[dict] = None,  # API item dict 전체 (Bio 수집에 사용)
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

        rule_from_original = (
            self.detect_language(original_title)
            if original_title else "und"
        )
        fallback_hint = subject_lang or rule_from_original or None

        # ── 비문학 전용: Bio 수집 (API-First) ───────────────────
        author_bio     = ""
        translator_bio = ""

        if not is_lit:
            _item = item or {}
            self._dbg("📘 [Bio] 비문학 판정 → Bio 수집 시작 (API-First)…")
            try:
                author_bio, translator_bio = self._scraper.fetch_bios(_item)
                if author_bio:
                    self._dbg(f"📘 [Bio] 저자 Bio 수집 완료 ({len(author_bio)}자)")
                if translator_bio:
                    self._dbg(f"📘 [Bio] 역자 Bio 수집 완료 ({len(translator_bio)}자)")
                if not author_bio and not translator_bio:
                    self._dbg("📘 [Bio] Bio 정보 없음 (API 미제공 + 크롤링 실패)")
            except Exception as e:
                self._dbg_err(f"Bio 크롤링 오류: {e}")

        # ── 파이프라인 정의 ──────────────────────────────
        if is_lit:
            # 문학: 규칙 우선 → GPT → 저자  (Bio 미사용)
            self._dbg("📘 [Pipeline] 문학 파이프라인 시작: Rule-based → GPT-General → Author-Hint")
            pipeline = [
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
                lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, label="GPT-General"),
                lambda: self._try_gpt_author(author, title, category_text, publisher, label="Author-Hint"),
            ]
        else:
            # 비문학: GPT(+Bio) 우선 → 규칙 → 저자(+Bio)
            self._dbg("📘 [Pipeline] 비문학 파이프라인 시작: GPT-General(+Bio) → Rule-based → Author-Hint(+Bio)")
            pipeline = [
                lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, author_bio=author_bio, translator_bio=translator_bio, label="GPT-General"),
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
                lambda: self._try_gpt_author(author, title, category_text, publisher, author_bio=author_bio, translator_bio=translator_bio, label="Author-Hint"),
            ]

        # ── 파이프라인 실행 — 결과가 나오면 즉시 반환 ───
        lang_h: Optional[str] = None
        author_hint: Optional[str] = None

        for i, step in enumerate(pipeline):
            result = step()
            if result:
                # Author-Hint 단계(마지막)는 author_hint로 별도 보관
                if i == len(pipeline) - 1:
                    author_hint = result
                else:
                    lang_h = result
                    break  # Early Return — 이후 단계 스킵

        # ── 충돌 조정 ────────────────────────────────────
        lang_h = self.reconcile_language(
            candidate=lang_h or "und",
            fallback_hint=fallback_hint,
            author_hint=author_hint,
        )
        self._dbg(f"📘 [결과] 조정 후 원서 언어(h) = {lang_h}")

        final = lang_h if lang_h in ALLOWED_CODES else "und"
        return final or "und"

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
        item_id   = str(item.get("itemId", "") or "")

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
            if self.is_domestic_category(category_text):
                self._dbg("📘 [판정] '국내도서' 감지 → $a=kor 강제")
                lang_a = "kor"

            # GPT 보조: und/eng일 때만 호출
            if lang_a in ("und", "eng"):
                self._dbg("📘 [설명] und/eng → GPT 본문 언어 재판정…")
                gpt_a = self.gpt_guess_main_lang(title, category_text, publisher)
                self._dbg(f"📘 [설명] GPT lang_a = {gpt_a}")
                lang_a = gpt_a if gpt_a in ALLOWED_CODES else "und"

            # ── $h: 원저 언어 ──────────────────────────────────
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
                item=item,           # ← item dict 전체 전달 (Bio 수집용)
            )
            self._dbg("📘 [결과] 최종 원서 언어(h) =", lang_h)

            # ── 태그 조합 ──────────────────────────────────────
            if lang_h and lang_h != lang_a and lang_h != "und":
                tag_041 = f"041 $a{lang_a} $h{lang_h}"
            else:
                tag_041 = f"041 $a{lang_a}"

            # 번역서($h)가 아니면 041/546 둘 다 생성하지 않음
            if "$h" not in tag_041:
                return None, None, original_title

            # 번역서일 때만 546 생성
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
        "041 $akor $hrus" → "러시아어 원작을 한국어로 번역"
        """
        a_codes: list[str] = []
        h_code:  Optional[str] = None

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

def _extract_code_and_reason(
    content: str,
    code_key: str = "$h",
) -> tuple[str, str, str]:
    """GPT 응답을 파싱해 (code, reason, signals) 튜플 반환."""
    code = reason = signals = ""
    for ln in [l.strip() for l in (content or "").splitlines() if l.strip()]:
        if ln.startswith(f"{code_key}="):
            code = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#reason="):
            reason = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#signals="):
            signals = ln.split("=", 1)[1].strip()
    return code or "und", reason, signals


def generate_546_from_041_kormarc(marc_041: str) -> str:
    """하위 호환용 모듈 레벨 래퍼."""
    return LangFieldBuilder.generate_546_from_041(marc_041)
