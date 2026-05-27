from __future__ import annotations

import re
import html
import time
import json
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
# 2. 역할 판별 및 API 헬퍼 함수
# ═══════════════════════════════════════════════════════════════

_TRANSLATOR_ROLE_STRICT: tuple[str, ...] = ("옮긴이", "역자", "옮김", "번역")
_WRITER_ROLE_KEYS:       tuple[str, ...] = ("지은이", "지음", "글", "저자")

_API_BIO_KEYS: tuple[str, ...] = (
    "authorBio", "biography", "authorIntro",
    "intro", "description", "authorDescription", "profile",
)

_BIO_DECOMPOSE_TAGS: tuple[str, ...] = (
    "script", "style", "meta", "noscript", "header", "footer",
    "nav", "aside", "menu", "form", "button", "input", "select",
    "label", "iframe", "link", "ul", "ol", "li", "a",
)

def _role_is_translator(role: str) -> bool:
    r = (role or "").strip()
    if not r: return False
    if any(m in r for m in _TRANSLATOR_ROLE_STRICT): return True
    if "역" in r and not any(x in r for x in ("지은이", "지음", "저자", "감수", "교정", "편집")):
        return True
    return False

def _role_is_writer(role: str) -> bool:
    r = (role or "").strip()
    return any(k in r for k in _WRITER_ROLE_KEYS)

def _collect_bio_from_api(item: dict, target_name: str) -> str:
    """API에서 '순수하게' 저자/역자 소개글만 수집합니다. 책 설명은 제외합니다."""
    chunks: list[str] = []
    sub = item.get("subInfo") or {}

    for auth in sub.get("authors") or []:
        if not isinstance(auth, dict): continue
        if target_name:
            name_in_api = (auth.get("authorName") or "").strip()
            if name_in_api != target_name.strip(): continue

        for key in _API_BIO_KEYS:
            val = auth.get(key)
            if isinstance(val, str) and val.strip():
                chunks.append(val.strip())

        for k, v in auth.items():
            if k in ("authorName", "authorId", "authorTypeDesc", "authorTypeName"):
                continue
            if isinstance(v, str) and len(v) > 40:
                chunks.append(v.strip())

    return "\n\n".join(dict.fromkeys(chunks))

def _parse_names_from_raw_author(raw_author: str, want_translator: bool) -> list[str]:
    names: list[str] = []
    translator_kw = ("옮긴이", "역자", "옮김", "역")
    writer_kw     = ("지은이", "지음", "글", "저자")

    for part in (raw_author or "").split(","):
        if want_translator:
            if not any(k in part for k in translator_kw): continue
            name = re.sub(r"\(.*?\)|옮긴이|역자|옮김|지은이|지음|저자|역", "", part, flags=re.I).strip()
        else:
            if not any(k in part for k in writer_kw): continue
            if any(k in part for k in translator_kw): continue
            name = re.sub(r"\(.*?\)|지은이|지음|글|저자|옮긴이|역자|옮김", "", part, flags=re.I).strip()
        if name:
            names.append(name)
    return list(dict.fromkeys(names))

def _extract_author_id_from_api(item: dict, target_name: str, want_translator: bool) -> Optional[int]:
    """API의 subInfo.authors에서 특정 이름의 authorId를 안전하게 추출합니다."""
    sub = item.get("subInfo") or {}
    for auth in sub.get("authors") or []:
        if not isinstance(auth, dict):
            continue
        
        # 1. 이름 확인
        name_in_api = (auth.get("authorName") or "").strip()
        if target_name and name_in_api != target_name.strip():
            continue
            
        # 2. 역할 확인 (저자인지 역자인지)
        role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "").strip()
        if want_translator and not _role_is_translator(role):
            continue
        if not want_translator and not _role_is_writer(role):
            continue
            
        # 3. ID 추출
        aid = auth.get("authorId")
        try:
            return int(aid) if aid is not None else None
        except (TypeError, ValueError):
            pass
    return None


# ═══════════════════════════════════════════════════════════════
# 3. AladinAuthorScraper  — API-First + 웹 크롤링 폴백
# ═══════════════════════════════════════════════════════════════

class AladinAuthorScraper:
    """
    저자/역자 소개글(Bio) 수집기 — API-First + 웹 크롤링 폴백.
    """

    _OVERVIEW_BASE = "https://www.aladin.co.kr/author/wauthor_overview.aspx"
    _HEADERS: dict[str, str] = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/124.0.0.0 Safari/537.36"
        ),
        "Accept":          "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8",
        "Referer":         "https://www.aladin.co.kr/",
    }
    _TIMEOUT    = 10    # seconds
    _RETRY      = 2
    _RETRY_WAIT = 1.0   # seconds

    def _get(self, url: str, params: Optional[dict] = None) -> Optional["requests.Response"]:
        """재시도 포함 GET. 실패 시 None 반환."""
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

    def scrape_author_bio_from_overview(self, author_id: int) -> str:
        """
        wauthor_overview.aspx?AuthorSearch=@{author_id} 에서 소개글을 긁어온다.
        """
        if not _SCRAPER_AVAILABLE or not author_id:
            return ""

        resp = self._get(self._OVERVIEW_BASE, params={"AuthorSearch": f"@{author_id}"})
        if resp is None:
            return ""

        soup = BeautifulSoup(resp.text, "html.parser")

        # 레이아웃/메뉴 태그 제거
        for tag_name in _BIO_DECOMPOSE_TAGS:
            for el in soup.find_all(tag_name):
                el.decompose()

        # 저자 소개 후보 영역 탐색 (id/class 힌트)
        root = soup
        for attr, pattern in (
            ("id",    re.compile(r"author|writer|profile|bio", re.I)),
            ("class", re.compile(r"author|writer|profile|bio|intro", re.I)),
        ):
            found = soup.find(attrs={attr: pattern})
            if found is not None:
                root = found
                break

        # p 태그 + 리프 div 에서 텍스트 수집
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

    def fetch_bios(self, item: dict) -> tuple[str, str]:
        """
        API-First 방식으로 저자·역자 Bio를 수집한다.
        """
        item = item or {}
        sub  = item.get("subInfo") or {}
        authors_list: list[dict] = [
            a for a in (sub.get("authors") or []) if isinstance(a, dict)
        ]

        # ── 저자(지은이) 이름 목록 결정 ────────────────────────
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

        # ── 역자 이름 목록 결정 ─────────────────────────────────
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
        names 목록의 첫 번째 인물부터 순서대로 시도해 비지 않은 Bio 를 하나 반환한다.
        """
        for name in names[:2]:
            api_bio = _collect_bio_from_api(item, name)
            if api_bio.strip() and len(api_bio.strip()) > 20:
                return api_bio.strip()

            if not _SCRAPER_AVAILABLE:
                continue
            aid = _extract_author_id_from_api(item, name, want_translator)
            if aid is None:
                continue
            web_bio = self.scrape_author_bio_from_overview(aid)
            if web_bio.strip():
                return web_bio.strip()

        return ""


# ═══════════════════════════════════════════════════════════════
# 4. LangFieldBuilder
# ═══════════════════════════════════════════════════════════════

class LangFieldBuilder:
    """
    041 / 546 필드 생성 전담 클래스.
    """

    LIT_KEYWORDS: dict[str, list[str]] = {
        "ko": ["문학", "소설", "시", "희곡"],
        "en": ["literature", "fiction", "novel", "poetry", "poem", "drama", "play"],
    }

    NONFICTION_KEYWORDS: dict[str, list[str]] = {
        "ko": ["역사", "근현대사", "서양사", "유럽사", "전기", "평전",
               "사회", "정치", "철학", "경제", "경영", "인문", "에세이", "수필"],
        "en": ["history", "biography", "memoir", "politics", "philosophy",
               "economics", "science", "technology", "nonfiction", "essay", "essays"],
    }

    SF_GUARD_KEYWORDS: dict[str, list[str]] = {
        "ko": ["과학", "기술"],
        "en": ["science", "technology"],
    }

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
    # GPT 판정 함수 (trans.py 스타일 JSON 구조 이식)
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
        if not self._client:
            return "und"

        system = """
당신은 한국어로 번역·출간된 외국 도서의 원서 언어(041 $h)를 ISDS 코드로 추정하는 사서용 AI입니다.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur, und

🚨[최우선 절대 규칙]
1. [국내도서≠한국어]: 카테고리가 '국내도서'라도 번역서일 수 있습니다.
2. [외국인 음차 주의]: '3D토털 퍼블리싱', '레오 톨스토이' 등 외국 인명/기관명이 한글로 적혀있다고 '한국 이름'으로 착각하여 kor 판정 절대 금지.
3. [번역자 존재]: 역자 정보가 있으면 한국어 원서가 아닐 확률이 높습니다. 역자가 한국인이라는 이유로 kor 판정을 내리지 마세요.
4. 불확실하면 임의 추정 대신 'und'를 반환하세요.

반드시 아래 JSON 형식으로만 응답하세요:
{
  "reasoning_process": "판단 근거 (한국어)",
  "inferred_code": "ISDS 코드 3자리"
}
"""
        payload = {
            "book": {"title": title, "original_title": original_title, "category": category, "publisher": publisher},
            "author": {"name": author, "bio_excerpt": author_bio[:1000] if author_bio else None},
            "translator": {"bio_excerpt": translator_bio[:1000] if translator_bio else None}
        }

        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": system.strip()},
                    {"role": "user", "content": json.dumps(payload, ensure_ascii=False)}
                ],
                response_format={"type": "json_object"},
                temperature=0,
            )
            obj = json.loads(resp.choices[0].message.content)
            code = obj.get("inferred_code", "und").lower()
            reason = obj.get("reasoning_process", "")

            if code not in ALLOWED_CODES: code = "und"
            self._dbg(f"🧭 [GPT 원서언어 JSON] $h={code}")
            if reason: self._dbg(f"🧭 [이유] {reason}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류: {e}")
            return "und"

    def gpt_guess_main_lang(
        self,
        title: str,
        category: str,
        publisher: str,
    ) -> str:
        if not self._client:
            return "und"

        system = """
본문 언어(041 $a)를 ISDS 코드로 추정하세요.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur, und

지침:
- 카테고리에 '국내도서'가 있거나 제목에 한글이 포함되면 대부분 'kor'입니다.
- 원작 언어가 아닌, 이 책 자체의 본문 언어를 판단하세요.

반드시 아래 JSON 형식으로 응답하세요:
{
  "reasoning_process": "판단 근거",
  "inferred_code": "ISDS 코드 3자리"
}
"""
        payload = {"title": title, "category": category, "publisher": publisher}
        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": system.strip()},
                    {"role": "user", "content": json.dumps(payload, ensure_ascii=False)}
                ],
                response_format={"type": "json_object"},
                temperature=0,
            )
            obj = json.loads(resp.choices[0].message.content)
            code = obj.get("inferred_code", "und").lower()
            if code not in ALLOWED_CODES: code = "und"
            self._dbg(f"🧭 [GPT 본문언어 JSON] $a={code}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류: {e}")
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
        if not self._client:
            return "und"

        system = """
저자 정보를 중심으로 원서 언어(041 $h)를 ISDS 코드로 추정하는 사서용 AI입니다.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur, und

🚨[최우선 절대 규칙]
1. [음차 주의]: '3D토털 퍼블리싱', '레오 톨스토이', '리처드 도킨스' 등 외국 기관/인명이 한글로 표기되었다고 한국 이름으로 간주하여 kor(한국어)로 판정하는 것을 절대 금지합니다.
2. [번역자 존재 = 외국어 원서]: 번역자 소개글이 존재한다는 것은 원서가 한국어가 아니라는 강력한 증거입니다.
3. [영어권 추정]: 저자 이름이 영미권(예: 퍼블리싱, 컴퍼니, 스미스 등)의 음차라면 'eng'를 우선 고려하세요.
4. 불확실하면 무조건 'und'를 반환하세요.

반드시 아래 JSON 형식으로만 응답하세요:
{
  "reasoning_process": "판단 근거 (한국어)",
  "inferred_code": "ISDS 코드 3자리"
}
"""
        payload = {
            "book": {"title": title, "category": category, "publisher": publisher},
            "author": {"name": author, "bio_excerpt": author_bio[:1000] if author_bio else None},
            "translator": {"bio_excerpt": translator_bio[:1000] if translator_bio else None}
        }

        try:
            resp = self._client.chat.completions.create(
                model=self._model,
                messages=[
                    {"role": "system", "content": system.strip()},
                    {"role": "user", "content": json.dumps(payload, ensure_ascii=False)}
                ],
                response_format={"type": "json_object"},
                temperature=0,
            )
            obj = json.loads(resp.choices[0].message.content)
            code = obj.get("inferred_code", "und").lower()
            reason = obj.get("reasoning_process", "")

            if code not in ALLOWED_CODES: code = "und"
            self._dbg(f"🧭 [GPT 저자기반 JSON] $h={code}")
            if reason: self._dbg(f"🧭 [이유] {reason}")
            return code
        except Exception as e:
            self._dbg_err(f"GPT 오류: {e}")
            return "und"

    # ─────────────────────────────────────────────
    # 규칙 기반 감지
    # ─────────────────────────────────────────────

    @staticmethod
    def detect_language_by_unicode(text: str) -> str:
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
        text = (text or "").lower()
        if initial_lang == 'chi' and re.search(r'[\u3040-\u30ff]', text):
            return 'jpn'
        if initial_lang in ('und', 'eng'):
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
        words = re.split(r'[>/\s]+', text or "")
        for w in words:
            for keywords, lang in LangFieldBuilder.CATEGORY_LANG_MAP:
                if any(kw in w for kw in keywords):
                    return lang
        return None

    # ─────────────────────────────────────────────
    # 카테고리 판정 유틸
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
    # $h 결정 로직
    # ─────────────────────────────────────────────

    def reconcile_language(
        self,
        candidate: str,
        fallback_hint: Optional[str] = None,
        author_hint:   Optional[str] = None,
    ) -> str:
        if author_hint and author_hint != "und" and author_hint != candidate:
            self._dbg(f"🔁 [조정] 저자기반({author_hint}) ≠ 1차({candidate}) → 저자기반 우선")
            return author_hint

        if fallback_hint and fallback_hint != "und" and fallback_hint != candidate:
            if candidate in {"ita", "fre", "spa", "por"} and fallback_hint == "eng":
                return candidate
            self._dbg(f"🔁 [조정] 규칙힌트({fallback_hint}) vs 1차({candidate}) → 규칙힌트 우선")
            return fallback_hint

        return candidate

    def _try_rule(
        self,
        subject_lang: str,
        rule_from_original: str,
        label: str = "Rule-based",
    ) -> Optional[str]:
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
        item: Optional[dict] = None,
    ) -> str:
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
            self._dbg("📘 [판정] 문학/비문학 단서 약함 → 추가 판단 진행.")

        rule_from_original = (
            self.detect_language(original_title)
            if original_title else "und"
        )
        fallback_hint = subject_lang or rule_from_original or None

        author_bio     = ""
        translator_bio = ""

        if not is_lit and item:
            self._dbg("📘 [Bio] 비문학 판정 → API-First Bio 수집 시작…")
            try:
                author_bio, translator_bio = self._scraper.fetch_bios(item)
                if author_bio:
                    self._dbg(f"📘 [Bio] 저자 Bio 수집 완료 ({len(author_bio)}자)")
                if translator_bio:
                    self._dbg(f"📘 [Bio] 역자 Bio 수집 완료 ({len(translator_bio)}자)")
                if not author_bio and not translator_bio:
                    self._dbg("📘 [Bio] Bio 정보 없음 (API 미제공 + 웹 폴백 실패)")
            except Exception as e:
                self._dbg_err(f"Bio 수집 오류: {e}")

        if is_lit:
            self._dbg("📘 [Pipeline] 문학 파이프라인 시작: Rule-based → GPT-General → Author-Hint")
            pipeline = [
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
                lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, label="GPT-General"),
                lambda: self._try_gpt_author(author, title, category_text, publisher, label="Author-Hint"),
            ]
        else:
            self._dbg("📘 [Pipeline] 비문학 파이프라인 시작: GPT-General(+Bio) → Rule-based → Author-Hint(+Bio)")
            pipeline = [
                lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, author_bio=author_bio, translator_bio=translator_bio, label="GPT-General"),
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
                lambda: self._try_gpt_author(author, title, category_text, publisher, author_bio=author_bio, translator_bio=translator_bio, label="Author-Hint"),
            ]

        lang_h: Optional[str] = None
        author_hint: Optional[str] = None

        for i, step in enumerate(pipeline):
            result = step()
            if result:
                if i == len(pipeline) - 1:
                    author_hint = result
                else:
                    lang_h = result
                    break

        lang_h = self.reconcile_language(
            candidate=lang_h or "und",
            fallback_hint=fallback_hint,
            author_hint=author_hint,
        )
        self._dbg(f"📘 [결과] 조정 후 원서 언어(h) = {lang_h}")

        final = lang_h if lang_h in ALLOWED_CODES else "und"
        return final or "und"

    # ─────────────────────────────────────────────
    # 최종 KORMARC 태그 생성 (메인 진입점)
    # ─────────────────────────────────────────────

    def get_kormarc_tags(
        self,
        item: dict,
        detail: dict,
    ) -> tuple[Optional[str], Optional[str], str]:
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
            or detail.get("category_text", "")
            or ""
        )

        try:
            lang_a = self.detect_language(title)
            self._dbg("📘 [DEBUG] 규칙 기반 1차 lang_a =", lang_a)

            if self.is_domestic_category(category_text):
                self._dbg("📘 [판정] '국내도서' 감지 → $a=kor 강제")
                lang_a = "kor"

            if lang_a in ("und", "eng"):
                self._dbg("📘 [설명] und/eng → GPT 본문 언어 재판정…")
                gpt_a = self.gpt_guess_main_lang(title, category_text, publisher)
                self._dbg(f"📘 [설명] GPT lang_a = {gpt_a}")
                lang_a = gpt_a if gpt_a in ALLOWED_CODES else "und"

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
            )
            self._dbg("📘 [결과] 최종 원서 언어(h) =", lang_h)

            if lang_h and lang_h != lang_a and lang_h != "und":
                tag_041 = f"041 $a{lang_a} $h{lang_h}"
            else:
                tag_041 = f"041 $a{lang_a}"

            if "$h" not in tag_041:
                return None, None, original_title

            tag_546 = self.generate_546_from_041(tag_041)
            return tag_041, tag_546, original_title

        except Exception as e:
            self._dbg(f"📕 [ERROR] get_kormarc_tags 예외: {e}")
            return f"📕 예외 발생: {e}", "", original_title

    # ─────────────────────────────────────────────
    # 546 텍스트 생성
    # ─────────────────────────────────────────────

    @staticmethod
    def generate_546_from_041(marc_041: str) -> str:
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
    # MRK 포맷 변환
    # ─────────────────────────────────────────────

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

    # ─────────────────────────────────────────────
    # 헬퍼
    # ─────────────────────────────────────────────

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
# 5. 모듈 레벨 순수 함수
# ═══════════════════════════════════════════════════════════════

def _extract_code_and_reason(
    content: str,
    code_key: str = "$h",
) -> tuple[str, str, str]:
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
    return LangFieldBuilder.generate_546_from_041(marc_041)