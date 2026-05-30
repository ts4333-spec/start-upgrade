"""
lang_field.py
─────────────────────────────────────────────────────────────────────────────
KORMARC 041(언어코드) · 546(언어주기) 필드 생성 모듈

【포함 기능】
  - ISDS 언어코드 상수 / 허용코드 집합
  - GPT 기반 언어 판정   : gpt_guess_original_lang()         (규칙 A~E 강화 프롬프트)
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
  - Safe Track           : AladinAuthorScraper.search_translator_catalog()
                           커리어 힌트 집계(_script_weights / _collapse_career_hints)
  - 최종 KORMARC 태그    : get_kormarc_tags()  → (tag_041, tag_546, orig_title)
  - 546 텍스트 생성       : generate_546_from_041_kormarc()
  - MRK 포맷 변환        : as_mrk_041(), as_mrk_546()
  - 헬퍼                 : extract_lang_h(), lang3_from_tag041()

【외부 의존】
  - openai.OpenAI 클라이언트 (client)   : 호출부에서 주입
  - dbg / dbg_err 로거                  : 호출부에서 주입 (없으면 print로 대체)
  - requests / BeautifulSoup            : pip install requests beautifulsoup4

【사용 예시】
    from lang_field import LangFieldBuilder

    builder = LangFieldBuilder(
        openai_client=client,
        ttbkey="TTBxxx",        # 알라딘 TTB 키 (Safe Track 역자 커리어 검색)
        dbg_fn=dbg,
        dbg_err_fn=dbg_err,
    )
    tag_041, tag_546, orig_title = builder.get_kormarc_tags(item, detail)
─────────────────────────────────────────────────────────────────────────────
"""

from __future__ import annotations

import re
import html
import json
import time
from collections import defaultdict
from typing import Callable, Dict, List, Mapping, MutableMapping, Optional, Tuple

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

# 한국어 언어명 → ISDS 코드 (Safe Track 커리어 힌트 → 코드 변환용)
_LANG_NAME_TO_ISDS: Dict[str, str] = {
    "영어": "eng", "일본어": "jpn", "중국어": "chi", "러시아어": "rus",
    "프랑스어": "fre", "독일어": "ger", "이탈리아어": "ita",
    "스페인어": "spa", "포르투갈어": "por", "터키어": "tur", "한국어": "kor",
}

# 알라딘 API
_ITEM_SEARCH_URL = "http://www.aladin.co.kr/ttb/api/ItemSearch.aspx"
_API_VERSION     = "20131101"

# 문자 체계 정규식 (trans.py 이식)
_RE_KANA  = re.compile(r"[\u3040-\u309F\u30A0-\u30FF]")
_RE_HAN   = re.compile(r"[\u4E00-\u9FFF]")
_RE_LATIN = re.compile(r"[A-Za-z]")

# 제목/설명 → 언어권 힌트 매핑 (trans.py COUNTRY_LANG_HINTS 이식)
_COUNTRY_LANG_HINTS: List[Tuple[str, str]] = [
    (r"영국|영어|영문|미국|American|English", "메타_영어권"),
    (r"일본|日|ジャパン",                     "메타_일본"),
    (r"중국|中文|汉语",                       "메타_중국"),
    (r"프랑스|프랑스어|French",               "메타_프랑스"),
    (r"독일|German|Deutsch",                  "메타_독일"),
    (r"이탈리아|Italian",                     "메타_이탈리아"),
    (r"스페인|Spanish|Español",               "메타_스페인"),
    (r"러시아|Russian|俄",                    "메타_러시아"),
    (r"한국|국내",                            "메타_한국"),
]

# 전공 → 언어명 규칙 (trans.py 이식)
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

# wauthor_overview HTML 정제 태그
_BIO_DECOMPOSE_TAGS: Tuple[str, ...] = (
    "script", "style", "meta", "noscript", "header", "footer",
    "nav", "aside", "menu", "form", "button", "input", "select",
    "label", "iframe", "link", "ul", "ol", "li", "a",
)
# AuthorSearch href ID 추출 정규식
_AUTHOR_SEARCH_HREF_RE = re.compile(r"AuthorSearch=(?:[^&]*?@)?(\d+)", re.I)

# API subInfo.authors Bio 필드 우선순위
_API_BIO_KEYS: Tuple[str, ...] = (
    "authorBio", "biography", "authorIntro",
    "intro", "description", "authorDescription", "profile",
)
_ITEM_DESC_KEYS: Tuple[str, ...] = (
    "fulldescription", "fullDescription", "Story", "story", "toc", "Toc",
)


# ═══════════════════════════════════════════════════════════════
# 2. 순수 함수 — 역할 판별 / 이름 파싱 / 커리어 분석
# ═══════════════════════════════════════════════════════════════

def _role_is_translator(role: str) -> bool:
    r = (role or "").strip()
    if not r:
        return False
    if any(m in r for m in ("옮긴이", "역자", "옮김", "번역")):
        return True
    if "역" in r and not any(x in r for x in ("지은이", "지음", "감수", "교정", "편집")):
        return True
    return False


def _role_is_writer(role: str) -> bool:
    r = (role or "").strip()
    return any(k in r for k in ("지은이", "지음", "글"))


def _parse_names_from_raw_author(raw_author: str, want_translator: bool) -> List[str]:
    """item['author'] 원시 문자열에서 역자 또는 저자 이름 파싱."""
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


def _parse_translator_names(author_raw: str) -> List[str]:
    """item['author'] 원시 문자열에서 역자 이름만 추출."""
    names: List[str] = []
    for part in (author_raw or "").split(","):
        if not re.search(r"옮긴이|역자|옮김|번역", part):
            continue
        name = re.sub(r"\(.*?\)|옮긴이|역자|옮김|번역", "", part, flags=re.I).strip()
        if name:
            names.append(name)
    return list(dict.fromkeys(names))


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


def _collect_bio_from_api(item: dict, target_name: str) -> str:
    """subInfo.authors 에서 target_name 의 소개글을 수집."""
    chunks: List[str] = []
    sub = item.get("subInfo") or {}
    for auth in sub.get("authors") or []:
        if not isinstance(auth, dict):
            continue
        if target_name and (auth.get("authorName") or "").strip() != target_name.strip():
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


def _extract_author_id_from_api(item: dict, target_name: str, want_translator: bool) -> Optional[int]:
    """subInfo.authors 에서 역할+이름 일치하는 authorId 반환."""
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


# ── 커리어 분석 함수 (trans.py 이식) ──────────────────────────

def _script_weights_on_text(text: str) -> Dict[str, float]:
    """텍스트의 문자 체계(가나·한자·라틴) 가중치 계산."""
    w: Dict[str, float] = {}
    if not text:
        return w
    if _RE_KANA.search(text):
        w["원제_가나(일본어)"]    = w.get("원제_가나(일본어)", 0.0)    + 2.0
    if _RE_HAN.search(text):
        w["원제_한자(중국어)"]    = w.get("원제_한자(중국어)", 0.0)    + 1.0
        w["원제_한자(일본어)"]    = w.get("원제_한자(일본어)", 0.0)    + 1.0
    if _RE_LATIN.search(text):
        w["원제_라틴(영미·유럽권)"] = w.get("원제_라틴(영미·유럽권)", 0.0) + 1.5
    return w


def _infer_signals_from_book(book: dict) -> Dict[str, float]:
    """번역작 1권에서 언어권 힌트 가중치를 추출한다."""
    title = (book.get("title") or "") + " " + (book.get("description") or "")
    sub   = book.get("subInfo") or {}
    ot    = (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
    blob  = f"{title} {ot}"

    hint_weights: MutableMapping[str, float] = defaultdict(float)
    for pat, label in _COUNTRY_LANG_HINTS:
        if re.search(pat, blob, re.I):
            hint_weights[label] += 1.0

    script_src = ot if ot else title
    for k, v in _script_weights_on_text(script_src).items():
        hint_weights[k] += v
    if ot and _RE_LATIN.search(ot) and not re.search(r"[가-힣]", ot):
        hint_weights["원제_라틴_보조(영어 가능)"] += 0.5

    return dict(hint_weights)


def _collapse_career_hints(hints: Mapping[str, float]) -> Dict[str, float]:
    """커리어 힌트 레이블 → 언어명으로 집계 (trans.py 이식)."""
    collapsed: MutableMapping[str, float] = defaultdict(float)
    for label, score in hints.items():
        if score <= 0:
            continue
        if label.startswith("메타_"):
            w = score * 0.6
            if "일본"    in label: collapsed["일본어"]    += w
            elif "중국"  in label: collapsed["중국어"]    += w
            elif "영어"  in label: collapsed["영어"]      += w
            elif "프랑스" in label: collapsed["프랑스어"] += w
            elif "독일"  in label: collapsed["독일어"]    += w
            elif "스페인" in label: collapsed["스페인어"] += w
            elif "이탈리아" in label: collapsed["이탈리아어"] += w
            elif "러시아" in label: collapsed["러시아어"] += w
            elif "한국"  in label: collapsed["한국어"]    += w
        else:
            if "가나"     in label: collapsed["일본어"]    += score
            elif "한자(중국" in label: collapsed["중국어"] += score
            elif "한자(일본" in label: collapsed["일본어"] += score
            elif "라틴" in label or "영미" in label: collapsed["영어"] += score
            elif "프랑스" in label: collapsed["프랑스어"] += score
            elif "독일"   in label: collapsed["독일어"]   += score
            elif "스페인" in label: collapsed["스페인어"] += score
            elif "이탈리아" in label: collapsed["이탈리아어"] += score
            elif "러시아" in label: collapsed["러시아어"] += score
            elif "한국"   in label: collapsed["한국어"]   += score
            elif "중동" in label or "아랍" in label: collapsed["아랍어권"] += score
            elif "북유럽" in label: collapsed["북유럽어권"] += score
            elif "포르투갈" in label: collapsed["포르투갈어"] += score
    return dict(collapsed)


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
    m = re.search(
        r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*"
        r"([가-힣A-Za-z·\s]{2,20}(?:학과|전공|학부|어과|어문학과?|문학과|사학과|과))",
        text,
    )
    if not m:
        m = re.search(
            r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*에서\s*"
            r"([가-힣A-Za-z·\s]{2,20}(?:학과|전공|학부|어과|어문학과?|문학과|사학과|과))",
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


# ═══════════════════════════════════════════════════════════════
# 3. AladinAuthorScraper — API-First + 웹 크롤링 + Safe Track
# ═══════════════════════════════════════════════════════════════

class AladinAuthorScraper:
    """
    저자/역자 소개글(Bio) 수집 + Safe Track 역자 커리어 검색.

    수집 우선순위
    ─────────────────────────────────────────────────────────────
    1순위 (API)      subInfo.authors[n].authorBio 등  (네트워크 0회)
    2순위 (웹·ID)    API authorId → wauthor_overview  (네트워크 1회)
    3순위 (웹·HTML)  wproduct HTML 이름 매칭 → wauthor_overview (최대 2회)

    Safe Track
    ─────────────────────────────────────────────────────────────
    search_translator_catalog(name, ttbkey)
      → 알라딘 ItemSearch로 역자 과거 번역작 최대 50권 검색
      → 각 책에서 문자 체계·메타 힌트 가중치 집계
      → (aggregated_hints, collapsed_hints, top_language) 반환
    """

    _WPRODUCT_BASE = "https://www.aladin.co.kr/shop/wproduct.aspx"
    _OVERVIEW_BASE = "https://www.aladin.co.kr/author/wauthor_overview.aspx"
    _HEADERS: Dict[str, str] = {
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

    # ── HTTP ─────────────────────────────────────────────────

    def _get(self, url: str, params: Optional[dict] = None) -> Optional["requests.Response"]:
        if not _SCRAPER_AVAILABLE:
            return None
        for attempt in range(self._RETRY):
            try:
                resp = requests.get(url, params=params, headers=self._HEADERS, timeout=self._TIMEOUT)
                resp.raise_for_status()
                return resp
            except Exception:
                if attempt < self._RETRY - 1:
                    time.sleep(self._RETRY_WAIT)
        return None

    def _get_json(self, url: str, params: dict) -> Optional[dict]:
        resp = self._get(url, params=params)
        if resp is None:
            return None
        try:
            return resp.json()
        except Exception:
            return None

    # ── AuthorId 파싱 ─────────────────────────────────────────

    @staticmethod
    def _extract_id_from_href(href: str) -> Optional[int]:
        if not href or "AuthorSearch=" not in href:
            return None
        m = _AUTHOR_SEARCH_HREF_RE.search(href)
        if not m:
            return None
        try:
            return int(m.group(1))
        except (TypeError, ValueError):
            return None

    def _resolve_id_from_html(self, page_html: str, target_name: str) -> Optional[int]:
        t = (target_name or "").strip()
        if not t or not page_html or not _SCRAPER_AVAILABLE:
            return None
        soup = BeautifulSoup(page_html, "html.parser")
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

    def _scrape_author_id_from_product(self, item: dict, target_name: str) -> Optional[int]:
        if not _SCRAPER_AVAILABLE:
            return None
        pid: Optional[str] = None
        for key in ("itemId", "item_id"):
            v = (item or {}).get(key)
            if v is not None and str(v).strip():
                pid = str(v).strip()
                break
        if not pid:
            isbn = ((item or {}).get("isbn13") or (item or {}).get("isbn") or "").replace("-", "").strip()
            pid = isbn or None
        if not pid:
            return None
        resp = self._get(self._WPRODUCT_BASE, params={"ItemId": pid})
        if resp is None:
            return None
        return self._resolve_id_from_html(resp.text, target_name)

    # ── wauthor_overview 크롤링 ──────────────────────────────

    def scrape_author_bio_from_overview(self, author_id: int) -> str:
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
        bio_text = "\n\n".join(dict.fromkeys(chunks))
        if not bio_text and root is not soup:
            for p in soup.find_all("p"):
                t = p.get_text(separator=" ", strip=True)
                if len(t) >= 8:
                    chunks.append(t)
            bio_text = "\n\n".join(dict.fromkeys(chunks))
        return bio_text[:1500] if bio_text else ""

    # ── Bio 수집 공개 인터페이스 ─────────────────────────────

    def fetch_bios(self, item: dict) -> Tuple[str, str]:
        """
        API-First 방식으로 저자·역자 Bio 수집.
        Step 1 API → Step 2 authorId 크롤링 → Step 3 상품HTML 이름매칭 크롤링
        """
        item = item or {}
        sub  = item.get("subInfo") or {}
        authors_list = [a for a in (sub.get("authors") or []) if isinstance(a, dict)]

        writer_names: List[str] = []
        for auth in authors_list:
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _role_is_writer(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    writer_names.append(n)
        if not writer_names:
            writer_names = _parse_names_from_raw_author(item.get("author") or "", want_translator=False)

        translator_names: List[str] = []
        for auth in authors_list:
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
            if _role_is_translator(role):
                n = (auth.get("authorName") or "").strip()
                if n:
                    translator_names.append(n)
        if not translator_names:
            translator_names = _parse_names_from_raw_author(item.get("author") or "", want_translator=True)

        author_bio     = self._fetch_single_bio(item, writer_names,     want_translator=False)
        translator_bio = self._fetch_single_bio(item, translator_names, want_translator=True)
        return author_bio, translator_bio

    def _fetch_single_bio(self, item: dict, names: List[str], want_translator: bool) -> str:
        for name in names[:2]:
            api_bio = _collect_bio_from_api(item, name)
            if api_bio.strip() and len(api_bio.strip()) > 5:
                return api_bio.strip()
            if not _SCRAPER_AVAILABLE:
                continue
            aid = _extract_author_id_from_api(item, name, want_translator)
            if aid is None:
                aid = self._scrape_author_id_from_product(item, name)
            if aid is None:
                continue
            web_bio = self.scrape_author_bio_from_overview(aid)
            if web_bio.strip():
                return web_bio.strip()
        return ""

    # ── Safe Track: 역자 커리어 검색 ─────────────────────────

    def search_translator_catalog(
        self,
        translator_name: str,
        ttbkey: str,
        max_results: int = 50,
        category_filter: Optional[str] = None,
    ) -> Tuple[Dict[str, float], Dict[str, float], Optional[str]]:
        """
        알라딘 ItemSearch로 역자 과거 번역작을 검색해 언어권 힌트를 집계한다.
        (trans.py item_search_translator_catalog + weighted_hint_counts 통합 이식)

        Parameters
        ----------
        translator_name  : 역자 표시명
        ttbkey           : 알라딘 TTB API 키
        max_results      : 검색 최대 결과 수 (기본 50)
        category_filter  : 같은 카테고리 책만 필터링할 상위 카테고리명 (None이면 전체)

        Returns
        -------
        (aggregated_hints, collapsed_hints, top_language)
          aggregated_hints : 레이블별 가중치 raw 합산  {"원제_가나(일본어)": 4.0, ...}
          collapsed_hints  : 언어명별 집계              {"일본어": 5.2, "영어": 1.5, ...}
          top_language     : 가장 높은 언어명            "일본어" | None
        """
        if not ttbkey or not translator_name.strip():
            return {}, {}, None

        params = {
            "ttbkey":       ttbkey.strip(),
            "QueryType":    "Author",
            "Query":        translator_name.strip(),
            "MaxResults":   str(max_results),
            "start":        "1",
            "SearchTarget": "Book",
            "output":       "js",
            "Version":      _API_VERSION,
            "OptResult":    "authors",
        }
        data = self._get_json(_ITEM_SEARCH_URL, params)
        if not data:
            return {}, {}, None

        books: List[dict] = data.get("item") or []

        # 동명이인 방지: 역자 역할 확인
        books = [b for b in books if self._book_is_translated_by(b, translator_name)]

        # 카테고리 필터링 (동명이인 방지 추가)
        if category_filter:
            filtered = [b for b in books if self._category_overlap(category_filter, b.get("categoryName") or "")]
            books = filtered if filtered else books  # 필터 후 빈 경우 전체 사용

        if not books:
            return {}, {}, None

        aggregated: Dict[str, float] = {}
        for b in books:
            for label, score in _infer_signals_from_book(b).items():
                aggregated[label] = aggregated.get(label, 0.0) + score

        collapsed   = _collapse_career_hints(aggregated)
        top_language = max(collapsed, key=lambda k: collapsed[k]) if collapsed else None

        # 한국어가 1위면 무시 (동명이인·국내서 오염 방지)
        if top_language == "한국어":
            remaining = {k: v for k, v in collapsed.items() if k != "한국어"}
            top_language = max(remaining, key=lambda k: remaining[k]) if remaining else None

        return aggregated, collapsed, top_language

    @staticmethod
    def _book_is_translated_by(book: dict, target_name: str) -> bool:
        """책의 역자가 target_name 인지 확인 (동명이인 방지)."""
        sub   = book.get("subInfo") or {}
        auths = sub.get("authors")
        if isinstance(auths, list) and auths:
            for auth in auths:
                if not isinstance(auth, dict):
                    continue
                if (auth.get("authorName") or "").strip() != target_name.strip():
                    continue
                role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
                if _role_is_translator(role):
                    return True
            return False
        # raw 문자열 폴백
        raw = book.get("author") or ""
        esc = re.escape(target_name.strip())
        return bool(re.search(rf"{esc}\s*\([^)]*(?:옮긴이|역자|옮김|역)[^)]*\)", raw))

    @staticmethod
    def _category_overlap(target: str, book_cat: str) -> bool:
        """대분류 첫 세그먼트 비교."""
        def segs(s: str) -> List[str]:
            s = s.replace("국내도서", "").replace("외국도서", "").replace("eBook", "")
            return [p.strip() for p in s.split(">") if p.strip()]
        ta, ba = segs(target), segs(book_cat)
        if not ta or not ba:
            return True
        return ta[0] == ba[0]


# ═══════════════════════════════════════════════════════════════
# 4. LangFieldBuilder
# ═══════════════════════════════════════════════════════════════

class LangFieldBuilder:
    """
    041 / 546 필드 생성 전담 클래스.

    Parameters
    ----------
    openai_client : OpenAI() 인스턴스. None이면 GPT 건너뜀.
    ttbkey        : 알라딘 TTB 키. Safe Track 역자 커리어 검색에 사용.
    model         : GPT 모델명 (기본 'gpt-4o').
    dbg_fn / dbg_err_fn : 로그 출력 함수 (기본 print).
    """

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
        dbg_fn:     Optional[Callable] = None,
        dbg_err_fn: Optional[Callable] = None,
    ):
        self._client  = openai_client
        self._ttbkey  = (ttbkey or "").strip()
        self._model   = model
        self._dbg     = dbg_fn     or (lambda *a: print("[DBG]",  *a))
        self._dbg_err = dbg_err_fn or (lambda *a: print("[ERR]",  *a))
        self._scraper = AladinAuthorScraper()

    # ─────────────────────────────────────────────────────────
    # GPT 판정 함수
    # ─────────────────────────────────────────────────────────

    # ── 강화 시스템 프롬프트 (규칙 A~E, trans.py 이식) ──────

    _SYSTEM_RULES_AE = (
        "당신은 **한국어로 번역·출간된 외국 도서**의 **원서 언어**만 추론하는 전문가입니다.\n"
        "입력은 알라딘 **번역서** 데이터입니다. 한국어 제목·'국내도서' 분류는 **번역본 유통 정보**일 뿐, "
        "원서가 한국어라는 증거가 **절대 아닙니다**.\n"
        "아래 [최우선 금지·강제 규칙]을 최우선 적용하세요. 예외 없음.\n\n"
        "══════════════════════════════════════════\n"
        "## [최우선] 절대 금지·강제 규칙\n"
        "══════════════════════════════════════════\n\n"
        "### 규칙 A. '국내도서' ≠ 한국어 원서\n"
        "분류에 '국내도서', '국내', '한국' 등이 있어도, 그것은 "
        "**한국 출판사가 번역·출간한 책**이라는 유통 분류일 뿐입니다.\n"
        "**절대 금지:** '국내도서'만 보고 한국어 원서 또는 한국을 원서 국가로 판정.\n"
        "국내도서는 원서 언어 추론의 **근거로 사용하지 마세요**.\n\n"
        "### 규칙 B. 외국인 이름 음차 — bio 부재여도 한국어 원서로 보지 말 것\n"
        "저자 소개글이 비어있어도, 이름이 외국 인명의 한글 음차이면 한국어 원서 판정 **절대 금지**.\n"
        "  · 예: 아나스타샤 메이블, 톰 스미스, 레오 톨스토이, 조지 오웰, 스티븐 킹 등\n"
        "  · 전형적 한국 성씨(김·이·박·최·정·강·조·윤·장·임)만 있는 이름이 아니면 외국인으로 간주.\n"
        "  · bio 부재를 이유로 'kor' 기본값 **금지**.\n\n"
        "### 규칙 D. 도서 제목의 결정적 고유명사 최우선 적용\n"
        "저자 정보가 부실해도, 제목·설명에 **특정 국가·문화권을 명확히 지시하는 고유명사**가 있으면 "
        "번역가 폴백보다 먼저 해당 본고장을 원서 언어로 **즉시** 판정하세요.\n"
        "  · 일본: 지브리, 라퓨타, 토토로, 모노노케, 미야자키 등 → jpn\n"
        "  · 미국: 마블, 디즈니, 픽사, 스타워즈, 해리포터 영미판 등 → eng\n"
        "  · 영국: 셜록, 007, 롤링 등 → eng\n\n"
        "### 규칙 C. 저자 단서 부실 시 번역가(역자) 폴백 **즉시·적극** 가동 (규칙 D 이후)\n"
        "규칙 D로 결론이 나지 않고 저자 단서가 부실할 때:\n"
        "  · 역자 소개글의 전공(불어과·노어과·일문학 등)을 최우선 단서로 수용\n"
        "  · 역자 커리어 힌트(career_hints)에서 누적 가중치가 큰 언어를 원서 언어로 채택\n"
        "  · 신호가 뚜렷하면 이를 원서 언어의 **주 결론**으로 사용\n\n"
        "### 규칙 E. 한국계·해외파 저자\n"
        "저자 이름이 한국식이어도, bio에 Stanford·Harvard·Forbes·NYT 등 영미권 기관·언론이 주축이면 "
        "해당 해외 언어로 판정하세요.\n\n"
        "## 추론 우선순위\n"
        "1순위: 저자(이름·소개글·문자 체계)\n"
        "2순위: 도서 메타(제목·원제) — 규칙 D 고유명사\n"
        "3순위: 역자(전공·커리어 힌트) — 규칙 C 조건에서만"
    )

    def gpt_guess_original_lang(
        self,
        title: str,
        category: str,
        publisher: str,
        author: str = "",
        original_title: str = "",
        author_bio: str = "",
        translator_bio: str = "",
        has_translator: bool = False,
        career_hints_text: str = "",   # Safe Track 커리어 힌트 텍스트 블록
    ) -> str:
        """원서 언어($h) 추정 — 규칙 A~E 강화 프롬프트. 불확실하면 'und'."""
        if not self._client:
            return "und"

        # 역자 블록
        translator_block = ""
        if has_translator:
            tr_names = _parse_translator_names(author)
            tr_str   = f": {', '.join(tr_names)}" if tr_names else " 있음"
            translator_block = f"\n- 역자(옮긴이{tr_str})"

        # Bio 블록
        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"

        # 커리어 힌트 블록
        career_block = ""
        if career_hints_text:
            career_block = f"\n- 역자 커리어 힌트(Safe Track): {career_hints_text}"

        # 번역서 전용 추가 지침
        translator_instruction = ""
        if has_translator:
            translator_instruction = (
                "\n- ★ 이 도서에는 역자(옮긴이)가 존재하는 번역서입니다."
                " 저자가 한국인이어도 외국어로 집필했을 수 있습니다."
                "\n- 역자 소개글의 전공(불어과·노어과·일문학 등)이 있으면 최우선 단서로 활용."
                "\n- 역자 커리어 힌트가 제공된 경우, 누적 가중치가 큰 언어를 원서 언어 후보로 적극 반영."
                "\n- 저자 이름·국적만으로 kor 단정 금지. 불확실하면 반드시 'und'."
            )

        prompt = f"""
아래 도서의 원서 언어(041 $h)를 ISDS 코드로 추정해줘.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

도서정보:
- 제목: {title}
- 원제: {original_title or "(없음)"}
- 분류: {category}
- 출판사: {publisher}
- 저자(지은이): {author}{translator_block}{bio_block}{career_block}

지침:
[규칙 A] '국내도서' 분류만으로 원서가 한국어라고 판정하는 것을 절대 금지.
[규칙 B] 저자 이름이 외국인 한글 음차인 경우, bio 부재여도 kor 판정 절대 금지.
[규칙 D] 제목·원제에 지브리·마블 등 결정적 고유명사가 있으면 즉시 해당 언어로 확정.
[규칙 C] 저자 단서가 부족하면 역자 전공·커리어 힌트를 최우선 단서로 활용.
[규칙 E] 저자 bio에 해외 대학·기관이 주축이면 해당 국가 언어로 판정.{translator_instruction}
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
                    {"role": "system", "content": self._SYSTEM_RULES_AE},
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

    def gpt_guess_main_lang(self, title: str, category: str, publisher: str) -> str:
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
            code, reason, _ = _extract_code_and_reason(content, "$a")
            if code not in ALLOWED_CODES:
                code = "und"
            self._dbg(f"🧭 [GPT 본문언어] $a={code}")
            if reason: self._dbg(f"🧭 [이유] {reason}")
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
        has_translator: bool = False,
        career_hints_text: str = "",
    ) -> str:
        """저자 기반 원서 언어($h) 추정 — 규칙 A~E 강화 프롬프트. 불확실하면 'und'."""
        if not self._client:
            return "und"

        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"

        career_block = ""
        if career_hints_text:
            career_block = f"\n- 역자 커리어 힌트(Safe Track): {career_hints_text}"

        translator_instruction = ""
        if has_translator:
            tr_names = _parse_translator_names(author)
            tr_str   = f": {', '.join(tr_names)}" if tr_names else " 있음"
            translator_instruction = (
                f"\n- ★ 이 도서에는 역자(옮긴이{tr_str})가 존재하는 번역서입니다."
                "\n- 저자가 한국인이어도 외국어로 집필했거나 외국에서 먼저 출판된 책일 수 있습니다."
                "\n- 저자 이름·국적만으로 kor 단정 금지. 불확실하면 반드시 'und'."
                "\n- 역자 전공·커리어 힌트가 제공된 경우, 이를 최우선 단서로 적극 활용."
            )

        prompt = f"""
저자 정보를 중심으로 원서 언어(041 $h)를 ISDS 코드로 추정.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

입력:
- 저자: {author}
- (참고) 제목: {title}
- (참고) 분류: {category}
- (참고) 출판사: {publisher}{bio_block}{career_block}

지침:
[규칙 A] '국내도서' 분류만으로 kor 판정 절대 금지.
[규칙 B] 외국인 한글 음차 이름 + bio 부재여도 kor 판정 절대 금지.
[규칙 C] 저자 단서 부족 시 역자 전공·커리어 힌트를 최우선으로 활용.
[규칙 D] 제목의 결정적 고유명사(지브리·마블 등)가 있으면 즉시 해당 언어로 확정.
[규칙 E] 저자 bio에 해외 대학·기관이 주축이면 해당 국가 언어로 판정.
- 저자 국적·주 집필 언어·대표 작품 원어를 우선.{translator_instruction}
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
                    {"role": "system", "content": self._SYSTEM_RULES_AE},
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

    # ─────────────────────────────────────────────────────────
    # 규칙 기반 감지
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
    # 카테고리 판정 유틸
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def tokenize_category(text: str) -> List[str]:
        if not text:
            return []
        t   = re.sub(r"[()]+", " ", text)
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

    # ─────────────────────────────────────────────────────────
    # 충돌 조정
    # ─────────────────────────────────────────────────────────

    def reconcile_language(
        self,
        candidate: str,
        fallback_hint: Optional[str] = None,
        author_hint:   Optional[str] = None,
        has_translator: bool = False,
    ) -> str:
        if author_hint and author_hint != "und" and author_hint != candidate:
            if has_translator and author_hint == "kor":
                self._dbg(f"🔁 [조정] 역자 있음 + author_hint=kor → 오판 차단, 후보({candidate}) 유지")
            else:
                self._dbg(f"🔁 [조정] 저자기반({author_hint}) ≠ 1차({candidate}) → 저자기반 우선")
                return author_hint

        if fallback_hint and fallback_hint != "und" and fallback_hint != candidate:
            if candidate in {"ita", "fre", "spa", "por"} and fallback_hint == "eng":
                return candidate
            self._dbg(f"🔁 [조정] 규칙힌트({fallback_hint}) vs 1차({candidate}) → 규칙힌트 우선")
            return fallback_hint

        return candidate

    # ─────────────────────────────────────────────────────────
    # 파이프라인 단계별 _try_* 메서드
    # ─────────────────────────────────────────────────────────

    def _try_rule(self, subject_lang: str, rule_from_original: str, label: str = "Rule-based") -> Optional[str]:
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
        has_translator: bool = False,
        career_hints_text: str = "",
        label: str = "GPT-General",
    ) -> Optional[str]:
        code = self.gpt_guess_original_lang(
            title, category_text, publisher, author, original_title,
            author_bio=author_bio, translator_bio=translator_bio,
            has_translator=has_translator, career_hints_text=career_hints_text,
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
        has_translator: bool = False,
        career_hints_text: str = "",
        label: str = "Author-Hint",
    ) -> Optional[str]:
        if not author:
            return None
        code = self.gpt_guess_original_lang_by_author(
            author, title, category_text, publisher,
            author_bio=author_bio, translator_bio=translator_bio,
            has_translator=has_translator, career_hints_text=career_hints_text,
        )
        # 역자 있는데 kor 반환 → 오판
        if has_translator and code == "kor":
            self._dbg(f"📘 [{label}] 역자 있음 + kor 반환 → 신뢰 불가, und 처리")
            return None
        if code and code != "und" and code in ALLOWED_CODES:
            self._dbg(f"📘 [{label}] 저자 기반 GPT 확정: {code}")
            return code
        self._dbg(f"📘 [{label}] 저자 기반 GPT 미확정 (결과: {code or 'und'})")
        return None

    # ─────────────────────────────────────────────────────────
    # Safe Track — 역자 커리어 힌트 텍스트 생성
    # ─────────────────────────────────────────────────────────

    def _run_safe_track(
        self,
        item: dict,
        translator_names: List[str],
        category_text: str,
    ) -> Tuple[str, Optional[str]]:
        """
        역자 이름 목록으로 커리어 검색 → 힌트 집계 → GPT 주입용 텍스트 생성.

        Returns
        -------
        (career_hints_text, top_language_isds)
          career_hints_text : GPT 프롬프트에 주입할 힌트 요약 문자열
          top_language_isds : 힌트에서 도출된 ISDS 코드 (없으면 None)
        """
        if not self._ttbkey or not translator_names:
            return "", None

        aggregated_all: Dict[str, float] = {}
        for name in translator_names[:2]:
            agg, collapsed, top = self._scraper.search_translator_catalog(
                translator_name=name,
                ttbkey=self._ttbkey,
                max_results=50,
                category_filter=category_text,
            )
            if not agg:
                continue
            self._dbg(f"📘 [SafeTrack] {name} 커리어 집계: top={top}, collapsed={collapsed}")
            for k, v in agg.items():
                aggregated_all[k] = aggregated_all.get(k, 0.0) + v

        if not aggregated_all:
            return "", None

        collapsed_all = _collapse_career_hints(aggregated_all)
        top_lang      = max(collapsed_all, key=lambda k: collapsed_all[k]) if collapsed_all else None
        if top_lang == "한국어":
            remaining = {k: v for k, v in collapsed_all.items() if k != "한국어"}
            top_lang  = max(remaining, key=lambda k: remaining[k]) if remaining else None

        # 상위 3개 언어 요약 텍스트
        top3 = sorted(collapsed_all.items(), key=lambda x: x[1], reverse=True)[:3]
        parts = [f"{lang}({score:.1f})" for lang, score in top3 if lang != "한국어"]
        hints_text = f"역자 과거 번역작 언어분포: {', '.join(parts)}" if parts else ""
        if top_lang and top_lang != "한국어":
            hints_text += f" → 추정 원서 언어: {top_lang}"

        isds = _LANG_NAME_TO_ISDS.get(top_lang or "") if top_lang else None
        if isds and isds not in ALLOWED_CODES:
            isds = None

        self._dbg(f"📘 [SafeTrack] 최종 힌트: {hints_text}")
        return hints_text, isds

    # ─────────────────────────────────────────────────────────
    # $h 결정 메인 로직
    # ─────────────────────────────────────────────────────────

    def determine_h_language(
        self,
        title: str,
        original_title: str,
        category_text: str,
        publisher: str,
        author: str,
        subject_lang: str,
        item_id: str = "",            # 하위 호환용 (미사용)
        item: Optional[dict] = None,  # API item dict (Bio 수집용)
        has_translator: bool = False,
    ) -> str:
        """
        원서 언어($h) 최종 결정 — 파이프라인 방식.

        문학 파이프라인  : Rule → GPT-General → Author-Hint
        비문학 파이프라인: Bio 수집 → [Safe Track] → GPT-General(+Bio+힌트)
                           → Rule → Author-Hint(+Bio+힌트)

        Safe Track(역자 커리어 검색)은 Bio 수집이 실패했거나
        단서가 부족할 때(author_bio + translator_bio 모두 짧을 때)만 실행.
        """
        lit_raw     = self.is_literature_category(category_text)
        nf_override = self.is_nonfiction_override(category_text)
        is_lit      = lit_raw and not nf_override

        if lit_raw and not nf_override:
            self._dbg("📘 [판정] 문학(소설/시/희곡 등) 성격이 뚜렷합니다.")
        elif lit_raw and nf_override:
            self._dbg("📘 [판정] 겉보기 문학 + 비문학 요소 → 비문학으로 처리.")
        elif not lit_raw and nf_override:
            self._dbg("📘 [판정] 비문학(역사·사회·철학 등) 성격이 강합니다.")
        else:
            self._dbg("📘 [판정] 문학/비문학 단서 약함 → 비문학 경로로 처리.")
            is_lit = False

        rule_from_original = self.detect_language(original_title) if original_title else "und"
        fallback_hint      = subject_lang or rule_from_original or None

        # ── 비문학 전용: Bio 수집 ──────────────────────────────
        author_bio = translator_bio = ""
        career_hints_text = ""
        top_career_isds: Optional[str] = None

        if not is_lit:
            _item = item or {}
            self._dbg("📘 [Bio] 비문학 → Bio 수집 시작 (API-First)…")
            try:
                author_bio, translator_bio = self._scraper.fetch_bios(_item)
                if author_bio:
                    self._dbg(f"📘 [Bio] 저자 Bio {len(author_bio)}자")
                if translator_bio:
                    self._dbg(f"📘 [Bio] 역자 Bio {len(translator_bio)}자")
                if not author_bio and not translator_bio:
                    self._dbg("📘 [Bio] Bio 없음 (API 미제공 + 크롤링 실패)")
            except Exception as e:
                self._dbg_err(f"Bio 수집 오류: {e}")

            # ── Safe Track: Bio가 없거나 단서 부족 시 역자 커리어 검색 ──
            bio_weak = (len(author_bio) + len(translator_bio)) < 80
            if has_translator and bio_weak and self._ttbkey:
                self._dbg("📘 [SafeTrack] Bio 단서 부족 → 역자 커리어 검색 시작…")
                tr_names = _parse_translator_names(author)
                if not tr_names:
                    sub = (_item.get("subInfo") or {})
                    for a in (sub.get("authors") or []):
                        if isinstance(a, dict) and _role_is_translator(
                            (a.get("authorTypeDesc") or a.get("authorTypeName") or "")
                        ):
                            n = (a.get("authorName") or "").strip()
                            if n:
                                tr_names.append(n)
                try:
                    career_hints_text, top_career_isds = self._run_safe_track(
                        _item, tr_names, category_text
                    )
                    if top_career_isds:
                        self._dbg(f"📘 [SafeTrack] 커리어 힌트 ISDS 도출: {top_career_isds}")
                except Exception as e:
                    self._dbg_err(f"Safe Track 오류: {e}")
            elif has_translator and not self._ttbkey:
                self._dbg("📘 [SafeTrack] ttbkey 없음 → 건너뜀")

        # ── 파이프라인 정의 ──────────────────────────────────
        if is_lit:
            self._dbg("📘 [Pipeline] 문학: Rule → GPT-General → Author-Hint")
            pipeline = [
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
                lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, has_translator=has_translator, label="GPT-General"),
                lambda: self._try_gpt_author(author, title, category_text, publisher, has_translator=has_translator, label="Author-Hint"),
            ]
        else:
            self._dbg("📘 [Pipeline] 비문학: GPT-General(+Bio+힌트) → Rule → Author-Hint(+Bio+힌트)")
            pipeline = [
                lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, author_bio=author_bio, translator_bio=translator_bio, has_translator=has_translator, career_hints_text=career_hints_text, label="GPT-General"),
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
                lambda: self._try_gpt_author(author, title, category_text, publisher, author_bio=author_bio, translator_bio=translator_bio, has_translator=has_translator, career_hints_text=career_hints_text, label="Author-Hint"),
            ]

        # ── 파이프라인 실행 ──────────────────────────────────
        lang_h: Optional[str]    = None
        author_hint: Optional[str] = None

        for i, step in enumerate(pipeline):
            result = step()
            if result:
                if i == len(pipeline) - 1:
                    author_hint = result
                else:
                    lang_h = result
                    break

        # ── 충돌 조정 ─────────────────────────────────────────
        lang_h = self.reconcile_language(
            candidate=lang_h or "und",
            fallback_hint=fallback_hint,
            author_hint=author_hint,
            has_translator=has_translator,
        )

        # ── Safe Track 커리어 힌트 최종 폴백 ─────────────────
        # GPT + 규칙 모두 und 이고, 커리어 힌트가 있으면 채택
        if (lang_h == "und" or lang_h not in ALLOWED_CODES) and top_career_isds:
            self._dbg(f"📘 [SafeTrack] GPT/Rule 모두 미확정 → 커리어 힌트 폴백: {top_career_isds}")
            lang_h = top_career_isds

        self._dbg(f"📘 [결과] 조정 후 원서 언어(h) = {lang_h}")
        return lang_h if lang_h in ALLOWED_CODES else "und"

    # ─────────────────────────────────────────────────────────
    # 메인 진입점: get_kormarc_tags
    # ─────────────────────────────────────────────────────────

    def get_kormarc_tags(
        self,
        item: dict,
        detail: dict,
    ) -> Tuple[Optional[str], Optional[str], str]:
        """
        알라딘 API item dict + 크롤링 detail dict →
        (tag_041, tag_546, original_title)

        번역서가 아닌 경우 : (None, None, original_title)
        번역서인 경우       : ("041 $akor $hfre", "프랑스어 원작을 한국어로 번역", original_title)
        예외 발생 시        : ("📕 예외: …", "", original_title)
        """
        item   = item   or {}
        detail = detail or {}

        title     = item.get("title",     "") or ""
        publisher = item.get("publisher", "") or ""
        author    = item.get("author",    "") or ""

        subinfo        = (item.get("subInfo") or {}) or {}
        original_title = html.unescape(subinfo.get("originalTitle", "") or "")
        if not original_title:
            original_title = detail.get("original_title", "") or ""

        subject_lang  = detail.get("subject_lang")
        category_text = (
            item.get("categoryText", "")
            or item.get("categoryName", "")
            or detail.get("category_text", "")
            or ""
        )

        try:
            # ── $a: 본문 언어 ──────────────────────────────────
            lang_a = self.detect_language(title)
            self._dbg("📘 [DEBUG] 규칙 기반 1차 lang_a =", lang_a)

            if self.is_domestic_category(category_text):
                self._dbg("📘 [판정] '국내도서' 감지 → $a=kor 강제")
                lang_a = "kor"

            if lang_a in ("und", "eng"):
                self._dbg("📘 [설명] und/eng → GPT 본문 언어 재판정…")
                gpt_a  = self.gpt_guess_main_lang(title, category_text, publisher)
                lang_a = gpt_a if gpt_a in ALLOWED_CODES else "und"

            # ── 역자 존재 여부 사전 감지 ───────────────────────
            has_translator = _has_translator_in_item(item)
            if has_translator:
                self._dbg("📘 [번역서감지] 역자(옮긴이) 존재 확인 → $h 판정 필수")

            self._dbg("📘 [DEBUG] 원제 감지됨:", bool(original_title), "| 원제:", original_title or "(없음)")
            self._dbg("📘 [DEBUG] 카테고리/크롤링 lang_h 후보 =", subject_lang or "(없음)")

            # ── $h: 원서 언어 파이프라인 ──────────────────────
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

            # ── 태그 조합 ──────────────────────────────────────
            # 역자 있는데 lang_h == lang_a → GPT 오판 보정
            if has_translator and lang_h == lang_a and lang_h != "und":
                self._dbg(
                    f"📘 [보정] 역자 있음 + lang_h({lang_h})==lang_a({lang_a})"
                    " → 원서 언어 미확정(und)으로 처리"
                )
                lang_h = "und"

            if lang_h and lang_h != lang_a and lang_h != "und":
                tag_041 = f"041 $a{lang_a} $h{lang_h}"
            else:
                tag_041 = f"041 $a{lang_a}"

            if "$h" not in tag_041:
                if has_translator:
                    self._dbg("⚠️ [경고] 역자가 있으나 원서 언어($h) 판정 실패 → None 반환")
                return None, None, original_title

            tag_546 = self.generate_546_from_041(tag_041)
            return tag_041, tag_546, original_title

        except Exception as e:
            self._dbg(f"📕 [ERROR] get_kormarc_tags 예외: {e}")
            return f"📕 예외 발생: {e}", "", original_title

    # ─────────────────────────────────────────────────────────
    # 546 텍스트 생성
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def generate_546_from_041(marc_041: str) -> str:
        """'041 $akor $hrus' → '러시아어 원작을 한국어로 번역'"""
        a_codes: List[str] = []
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

    # ─────────────────────────────────────────────────────────
    # MRK 포맷 변환
    # ─────────────────────────────────────────────────────────

    @staticmethod
    def as_mrk_041(tag_041: Optional[str]) -> Optional[str]:
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
    # 헬퍼
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
# 5. 모듈 레벨 하위 호환 래퍼
# ═══════════════════════════════════════════════════════════════

def generate_546_from_041_kormarc(marc_041: str) -> str:
    return LangFieldBuilder.generate_546_from_041(marc_041)
