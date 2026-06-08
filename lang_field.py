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
import json
import time
import urllib.parse
from collections import defaultdict
from typing import Any, Callable, Dict, List, Mapping, MutableMapping, Optional, Tuple

try:
    import requests
    from bs4 import BeautifulSoup
    _SCRAPER_AVAILABLE = True
except ImportError:
    _SCRAPER_AVAILABLE = False

try:
    from lingua import Language as _LinguaLanguage, LanguageDetectorBuilder as _LinguaBuilder
    _LINGUA_AVAILABLE = True
except ImportError:
    _LINGUA_AVAILABLE = False


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
_API_VERSION     = "20131101"

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

# ── lingua 어휘 사전 기반 언어 감지 ──────────────────────────────────────
# lingua는 글자가 아닌 단어 단위 어휘 매칭으로 언어를 판별하므로
# 규칙 기반 CHAR_LANG_MAP(글자 단위)의 대체재로 사용한다.
if _LINGUA_AVAILABLE:
    _LINGUA_DETECTOR = _LinguaBuilder.from_all_languages().build()
else:
    _LINGUA_DETECTOR = None

# lingua Language → ISDS 코드 매핑
_LINGUA_TO_ISDS: Dict[Any, str] = {}
if _LINGUA_AVAILABLE:
    _LINGUA_TO_ISDS = {
        _LinguaLanguage.ENGLISH:    "eng", _LinguaLanguage.FRENCH:     "fre",
        _LinguaLanguage.DUTCH:      "dut", _LinguaLanguage.SPANISH:    "spa",
        _LinguaLanguage.PORTUGUESE: "por", _LinguaLanguage.GERMAN:     "ger",
        _LinguaLanguage.ITALIAN:    "ita", _LinguaLanguage.SWEDISH:    "swe",
        _LinguaLanguage.BOKMAL:     "nor", _LinguaLanguage.NYNORSK:    "nor",
        _LinguaLanguage.DANISH:     "dan", _LinguaLanguage.FINNISH:    "fin",
        _LinguaLanguage.POLISH:     "pol", _LinguaLanguage.CZECH:      "cze",
        _LinguaLanguage.HUNGARIAN:  "hun", _LinguaLanguage.ROMANIAN:   "rum",
    }

_LINGUA_ANCHOR_THRESHOLD = 0.97  # 단어 하나가 이 신뢰도 이상이면 앵커 단어로 확정
_LINGUA_TITLE_THRESHOLD  = 0.80  # 전체 제목 신뢰도 — 앵커 없을 때 보조 판정
_LINGUA_LONG_THRESHOLD   = 0.55  # 5단어 이상 긴 제목에 완화 적용하는 신뢰도
_LINGUA_SINGLE_THRESHOLD = 0.15  # 1단어 원제 전용 — 극도로 완화된 threshold
_LINGUA_SINGLE_GAP       = 0.08  # 1단어 원제: 1위-2위 신뢰도 최소 격차 (모호어 걸러냄)

# 언어별 기능어(전치사·관사·접속사) — 다른 언어에 쓰이지 않는 고유 기능어만 포함
# 기능어가 하나라도 감지되면 해당 언어로 즉시 확정 (어휘 앵커보다 우선)
_FUNCTION_WORDS: Dict[str, set] = {
    "eng": {"the","a","an","how","and","into","with","of","for","by","from",
             "in","on","at","it","its","this","that","those","these",
             "is","are","was","were","been","to","or","but","if","as",
             "its","their","there","they","we","he","she","be","about",
             "after","before","between","through","under","over","up","out"},
    "fre": {"une","au","aux","du","des","les","dans","sur","pour","par","avec",
             "sans","sous","vers","dont","qui","que","cet","cette",
             "mais","donc","car","ni"},
    "ita": {"della","delle","degli","nel","nella","nelle","negli","dal",
             "dalla","dalle","dagli","sul","sulla","sulle","sugli",
             "per","tra","fra","una","uno","gli","questo","questa"},
    "spa": {"del","los","las","unos","unas","con","sin","sobre","entre",
             "desde","hasta","hacia","durante","para",
             "pero","sino","aunque","porque"},
    "dut": {"het","een","van","voor","naar","met","over","aan","bij","uit",
             "door","zonder","tegen","tijdens","omdat","maar","want"},
    "ger": {"der","die","das","ein","eine","und","oder","aber","denn","weil",
             "dass","wenn","als","durch","für","mit","von","bei","nach","über"},
    "por": {"uma","uns","umas","do","da","dos","das","no","na","nos","nas",
             "pelo","pela","pelos","pelas","com","sem","sobre","para"},
    "nor": {"og","eller","men","som","til","fra","med","uten","over",
             "under","mellom","gjennom","fordi","hvis"},
    "swe": {"och","eller","men","för","som","till","från","med","utan","över",
             "under","mellan","genom","eftersom","om"},
    "dan": {"og","eller","men","som","til","fra","med","uden","over",
             "under","mellem","gennem","fordi","hvis"},
}

# ── 제목/설명 → 언어권 힌트 레이블 매핑 (trans.py COUNTRY_LANG_HINTS 이식) ──
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


def _infer_signals_from_book(book: Dict) -> Dict[str, float]:
    """번역작 1권에서 언어권 힌트 가중치 추출 (trans.py infer_signals_from_book 이식)."""
    title = (book.get("title") or "") + " " + (book.get("description") or "")
    sub   = book.get("subInfo") or {}
    ot    = (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
    blob  = f"{title} {ot}"

    hw: MutableMapping[str, float] = defaultdict(float)
    for pat, label in _COUNTRY_LANG_HINTS:
        if re.search(pat, blob, re.I):
            hw[label] += 1.0
    script_src = ot if ot else title
    for k, v in _script_weights_on_text(script_src).items():
        hw[k] += v
    if ot and _RE_LATIN.search(ot) and not re.search(r"[가-힣]", ot):
        hw["원제_라틴_보조(영어 가능)"] += 0.5
    return dict(hw)


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

    def _get_json(self, url: str, params: dict) -> Optional[Dict]:
        """JSON GET 헬퍼. 실패 시 None."""
        resp = self._get(url, params=params)
        if resp is None:
            return None
        try:
            return resp.json()
        except Exception:
            return None

    # ── Safe Track: 역자 커리어 검색 ─────────────────────────

    def search_translator_catalog(
        self,
        translator_name: str,
        ttbkey: str,
        max_results: int = 50,
        category_filter: Optional[str] = None,
    ) -> Tuple[Dict[str, float], int]:
        """
        ItemSearch로 역자 과거 번역작(최대 50권)을 검색해
        raw career_hint_counts(레이블별 가중치 합산)를 반환한다.
        (trans.py item_search_translator_catalog + weighted_hint_counts 통합)

        Returns
        -------
        (career_hint_counts, filtered_book_count)
          career_hint_counts : {"원제_가나(일본어)": 4.0, "메타_프랑스": 2.0, ...}
            ★ _collapse 하지 않은 raw dict — GPT가 직접 해석하게 한다
          filtered_book_count : 동명이인 필터 후 집계에 사용된 책 수
        """
        if not ttbkey or not translator_name.strip():
            return {}, 0

        data = self._get_json(_ITEM_SEARCH_URL, {
            "ttbkey":       ttbkey.strip(),
            "QueryType":    "Author",
            "Query":        translator_name.strip(),
            "MaxResults":   str(max_results),
            "start":        "1",
            "SearchTarget": "Book",
            "output":       "js",
            "Version":      _API_VERSION,
            "OptResult":    "authors",
        })
        if not data:
            return {}, 0

        books: List[Dict] = data.get("item") or []

        # 동명이인 방지: 역자 역할 확인
        books = [b for b in books if self._book_is_translated_by(b, translator_name)]

        # 카테고리 필터
        if category_filter:
            filtered = [b for b in books if self._category_overlap(
                category_filter, b.get("categoryName") or ""
            )]
            if filtered:
                books = filtered   # 필터 후 빈 경우 전체 사용

        if not books:
            return {}, 0

        counts: Dict[str, float] = {}
        for b in books:
            for label, score in _infer_signals_from_book(b).items():
                counts[label] = counts.get(label, 0.0) + score

        return counts, len(books)

    @staticmethod
    def _book_is_translated_by(book: Dict, target_name: str) -> bool:
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
    # ⚠️  각 언어에 진짜 전용인 마커만 남김
    #   · à·è·ì·ò·ù  → 이탈리아어와 공유 → 프랑스어 항목에서 제외
    #   · á·í·ó·ú    → 스페인어·포르투갈어·카탈루냐어 공유 → 스페인어 항목에서 제외
    #   · ñ          → 스페인어 전용
    #   · ã·õ        → 포르투갈어 전용
    #   · ç·œ·ê·û    → 프랑스어 전용
    CHAR_LANG_MAP: list[tuple[str, str]] = [
        ("çœêû", "fre"),   # 프랑스어 전용 마커
        ("ñ",     "spa"),   # 스페인어 전용 마커
        ("ãõ",    "por"),   # 포르투갈어 전용 마커
    ]

    def __init__(
        self,
        openai_client=None,
        model: str = "gpt-4o",
        dbg_fn:     Optional[Callable] = None,
        dbg_err_fn: Optional[Callable] = None,
        ttbkey: str = "",   # 알라딘 TTB 키 — Safe Track 역자 커리어 검색에 사용
    ):
        self._client  = openai_client
        self._model   = model
        self._ttbkey  = (ttbkey or "").strip()
        self._dbg     = dbg_fn     or (lambda *a: print("[DBG]",  *a))
        self._dbg_err = dbg_err_fn or (lambda *a: print("[ERR]",  *a))
        self._scraper = AladinAuthorScraper()

    # ─────────────────────────────────────────────
    # 2-1. GPT 판정 함수
    # ─────────────────────────────────────────────

    def _lingua_detect_latin_title(self, title: str) -> tuple[str, str]:
        """
        lingua 어휘 사전으로 라틴 문자 원제의 언어를 단어 단위로 판별.

        반환: (isds_code, reason)
          - isds_code: 확정 코드 또는 "und" (불확실)
          - reason:    판정 근거 (디버그용 한국어 문자열)

        판별 순서:
          1) 기능어 앵커: 전치사·관사·접속사 등 언어 전용 기능어 감지 → 즉시 확정
          2) 단어별 어휘 앵커: 신뢰도 ≥ ANCHOR_THRESHOLD 인 단어 → 즉시 확정
          3) 5단어 이상 긴 제목: lingua 신뢰도 ≥ LONG_THRESHOLD → 확정
          4) 전체 제목 신뢰도: ≥ TITLE_THRESHOLD → 보조 확정
          5) 모두 실패 → "und" → GPT 위임
        """
        if not _LINGUA_AVAILABLE or _LINGUA_DETECTOR is None:
            return "und", "lingua 미설치"

        lower_words = re.findall(r"[^\s,;:·.!?]+", title.lower())
        orig_words  = re.findall(r"[^\s,;:·.!?]+", title)

        # ── 0단계: 1단어 원제 전용 패스트트랙 ─────────────────────────────
        # 1단어는 비율 계산 불가 → 신뢰도+격차 조건으로 직접 판정
        # 조건: 1위 신뢰도 ≥ _LINGUA_SINGLE_THRESHOLD AND 1위-2위 격차 ≥ _LINGUA_SINGLE_GAP
        # 조건 미충족 → und (모호어, GPT에 위임)
        if len(orig_words) == 1:
            vals = _LINGUA_DETECTOR.compute_language_confidence_values(orig_words[0])
            if (vals
                    and vals[0].value >= _LINGUA_SINGLE_THRESHOLD
                    and (len(vals) < 2 or vals[0].value - vals[1].value >= _LINGUA_SINGLE_GAP)):
                code = _LINGUA_TO_ISDS.get(vals[0].language, "und")
                if code != "und":
                    return code, (
                        f"1단어 패스트트랙 '{orig_words[0]}' → "
                        f"{vals[0].language.name} ({vals[0].value:.3f}, "
                        f"2위와 격차 {vals[0].value - vals[1].value:.3f})"
                        if len(vals) > 1 else
                        f"1단어 패스트트랙 '{orig_words[0]}' → "
                        f"{vals[0].language.name} ({vals[0].value:.3f})"
                    )
            return "und", f"1단어 모호 → GPT 위임"
        for lang, func_set in _FUNCTION_WORDS.items():
            hits = [w for w in lower_words if w in func_set]
            if hits:
                return lang, f"기능어 앵커({lang}): {hits[:3]}"

        # 2단계: 단어별 어휘 앵커
        for word in orig_words:
            vals = _LINGUA_DETECTOR.compute_language_confidence_values(word)
            if vals and vals[0].value >= _LINGUA_ANCHOR_THRESHOLD:
                code = _LINGUA_TO_ISDS.get(vals[0].language, "und")
                if code != "und":
                    return code, (
                        f"어휘 앵커 '{word}' → "
                        f"{vals[0].language.name} ({vals[0].value:.2f})"
                    )

        # 3단계: 5단어 이상 긴 제목 — 완화된 threshold 적용
        if len(orig_words) >= 5:
            vals = _LINGUA_DETECTOR.compute_language_confidence_values(title)
            if vals and vals[0].value >= _LINGUA_LONG_THRESHOLD:
                code = _LINGUA_TO_ISDS.get(vals[0].language, "und")
                if code != "und":
                    return code, (
                        f"5단어+ 제목 → "
                        f"{vals[0].language.name} ({vals[0].value:.2f})"
                    )

        # 4단계: 전체 제목 신뢰도
        vals = _LINGUA_DETECTOR.compute_language_confidence_values(title)
        if vals and vals[0].value >= _LINGUA_TITLE_THRESHOLD:
            code = _LINGUA_TO_ISDS.get(vals[0].language, "und")
            if code != "und":
                return code, (
                    f"전체 제목 → "
                    f"{vals[0].language.name} ({vals[0].value:.2f})"
                )

        return "und", "앵커 없음·신뢰도 부족 → GPT 위임"

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

        # ── 1차: lingua 어휘 사전 판별 (글자 단위 아닌 단어 단위) ──────────
        lingua_code, lingua_reason = self._lingua_detect_latin_title(title)
        if lingua_code != "und":
            self._dbg(f"🔬 [원제lingua] '{title}' → {lingua_code} ({lingua_reason})")
            return lingua_code
        self._dbg(f"🔬 [원제lingua] {lingua_reason} → GPT 호출")

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

            "4. 【최우선】기능어 앵커:\n"
            "   전치사·관사·접속사 등 특정 언어 고유의 기능어(Functional Words)가 하나라도\n"
            "   있으면 다른 단어들이 외래어로 겹치든 무관하게 즉시 해당 언어로 확정하십시오.\n"
            "   기능어는 어휘 단어보다 훨씬 강력한 언어 식별자입니다.\n"
            "   - 영어 기능어: a, an, the, how, and, in, on, at, into, with, of, for,\n"
            "                  by, from, it, is, are, was, were, to, or, but, if, as,\n"
            "                  this, that, about, after, before, through, up, out\n"
            "                  ★ 대소문자 무관: 'A', 'At', 'In', 'On'도 모두 영어 기능어\n"
            "   - 프랑스어:    une, au, aux, du, des, les, dans, sur, pour, par, avec,\n"
            "                  sans, sous, dont, qui, que, mais, donc\n"
            "   - 이탈리아어:  della, delle, degli, nel, nella, dal, dalla, sul, sulla,\n"
            "                  per, tra, fra, uno, gli, questo, questa\n"
            "   - 스페인어:    del, los, las, unos, con, sin, sobre, desde, hasta, para,\n"
            "                  pero, sino, aunque, porque\n"
            "   - 네덜란드어:  het, een, van, voor, naar, met, over, aan, bij, uit, door\n"
            "   - 독일어:      der, die, das, ein, eine, und, oder, aber, denn, weil,\n"
            "                  dass, wenn, als, durch, für, mit, von, bei, nach, über\n"
            "   - 예: 'The Formula How Rogues and Speed Freaks Reengineered F1'\n"
            "         → 'The'·'How'·'and' 는 영어 기능어 → 즉시 eng 확정\n"
            "   - 예: 'A Naturalist at Large'\n"
            "         → 'a'·'at' 은 영어 기능어(대소문자 무관) → 즉시 eng 확정\n"
            "   - 예: 'In Cold Blood' → 'in' 은 영어 기능어 → 즉시 eng 확정\n\n"

            "3-1. 【짧은 제목(4단어 이하) 특별 규칙】:\n"
            "   단어가 4개 이하일 때 비율 계산 오류 방지: 아래 중 하나라도 해당하면\n"
            "   수학 계산 없이 즉시 확정하십시오.\n"
            "   - 기능어가 하나라도 포함된 경우\n"
            "   - 동일 언어로 확인된 단어가 2개 이상인 경우\n"
            "   - 예: ['A'→eng기능어, 'Naturalist'→eng, 'at'→eng기능어, 'Large'→eng]\n"
            "         → 기능어 2개, eng 4개 → 계산 없이 즉시 eng 확정\n\n"


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
            "eng, fre, dut, spa, por, ger, ita, swe, nor, dan, fin, pol, cze, hun, rum, und\n\n"

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
    ) -> str:
        """원서 언어($h) 추정. 불확실하면 'und'."""
        if not self._client:
            return "und"

        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"

        translator_block = ""
        translator_instruction = ""
        if has_translator:
            tr_names = _parse_translator_names(author)
            tr_str = f": {', '.join(tr_names)}" if tr_names else " 있음"
            translator_block = f"\n- 역자(옮긴이{tr_str})"
            translator_instruction = (
                "\n- ★ 이 도서에는 역자(옮긴이)가 존재하는 번역서입니다."
                " 저자가 한국인이어도 외국어로 집필했을 수 있습니다."
                "\n- 역자 소개글의 전공(불어과·노어과·일문학 등)이 있으면 최우선 단서로 활용."
                "\n- 저자 이름·국적만으로 kor 단정 금지. 불확실하면 반드시 'und'."
            )

        prompt = f"""
아래 도서의 원서 언어(041 $h)를 ISDS 코드로 추정해줘.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur, dut 등

도서정보:
- 제목: {title}
- 원제: {original_title or "(없음)"}
- 분류: {category}
- 출판사: {publisher}
- 저자(지은이): {author}{translator_block}{bio_block}

지침:
[★ 라틴어권 원제(Original Title) 단어 단위 분석 규칙]
1. 원제가 라틴 알파벳으로 이루어진 경우, 반드시 '단어(Word)' 단위로 쪼개어 각 단어가 어느 언어 사전에 존재하는지 교집합을 분석할 것.
2. 1단어 모호성: 원제가 단 1개의 단어이고, 2개 이상 언어에서 범용적으로 쓰이는 경우(예: 'Chat', 'De' 등), 절대 임의로 판정하지 말고 'und'(판단 보류) 처리.
3. 2단어 모호성: 2개 단어 모두 여러 언어에서 중복으로 쓰여 확정할 수 없는 경우 'und' 처리. 단, "De(모호함) + Bourgondiërs(네덜란드어 고유)"처럼 조합을 통해 특정 언어로 확정이 가능해진다면 해당 코드로 판정.
4. 명확한 판정: 특정 언어만의 고유한 철자법, 억양 기호(Diacritics), 또는 어휘가 포함되어 특정이 명확하다면 해당 ISDS 코드 판정.

[일반 지침]
- 국가/지역을 언어로 곧바로 치환하지 말 것.
- 저자 국적·주 집필 언어·최초 출간 언어를 우선 고려.
- 저자/역자 소개글이 제공된 경우 국적·활동국·집필 언어 단서를 우선 활용.{translator_instruction}
- 불확실하거나 위의 모호성 규칙에 해당하면 임의 추정 대신 반드시 'und' 사용.

출력형식(정확히 이 2~3줄):
$h=[ISDS 코드 또는 und]
#reason=[단어 단위 분리 및 분석 결과, 모호성 판단 여부를 포함한 짧은 요약]
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
        has_translator: bool = False,
    ) -> str:
        """저자 정보 기반 원서 언어($h) 추정. 불확실하면 'und'."""
        if not self._client:
            return "und"

        bio_block = ""
        if author_bio:
            bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        if translator_bio:
            bio_block += f"\n- 역자 소개글: {translator_bio[:400]}"

        translator_instruction = ""
        if has_translator:
            tr_names = _parse_translator_names(author)
            tr_str = f": {', '.join(tr_names)}" if tr_names else " 있음"
            translator_instruction = (
                f"\n- ★ 이 도서에는 역자(옮긴이{tr_str})가 존재하는 번역서입니다."
                "\n- 저자가 한국인이어도 외국어로 집필했거나 외국에서 먼저 출판된 책일 수 있습니다."
                "\n- 저자 이름·국적만으로 kor 단정 금지. 불확실하면 반드시 'und'."
                "\n- 역자 소개글의 전공(불어과·노어과·일문학 등)이 있으면 최우선 단서로 활용."
            )

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
- 국가=언어 단순 치환 금지.{translator_instruction}
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
            "bio_excerpt":    bio_s[:3000] if bio_s else None,
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
            "bio_excerpt":      bio_s[:3000] if bio_s else None,
            "univ_major_regex": extract_univ_major_regex(bio_s) if bio_s else None,
        }

    # ─────────────────────────────────────────────
    # 2-1c. 비문학 전용 JSON Payload GPT 판정
    # ─────────────────────────────────────────────

    # 시스템 프롬프트 — trans.py determine_origin_country_by_llm 원문 그대로 이식
    _NONFICTION_SYSTEM_PROMPT: str = (
        "당신은 **한국어로 번역·출간된 외국 도서**의 **원서 언어·원서 국가**만 추론하는 전문가입니다.\n"
        "입력은 알라딘 **번역서** 데이터입니다. 한국어 제목·'국내도서' 분류는 **번역본 유통 정보**일 뿐, "
        "원서가 한국어라는 증거가 **절대 아닙니다**.\n"
        "아래 [최우선 금지·강제 규칙]을 최우선 적용하세요. 예외 없음.\n\n"
        "══════════════════════════════════════════════════════\n"
        "## [최우선] 절대 금지·강제 규칙\n"
        "══════════════════════════════════════════════════════\n\n"
        "### 규칙 A. '국내도서' ≠ 한국어 원서\n"
        "categoryName의 '국내도서'·'국내'·'한국'은 한국 출판사의 **유통 분류**일 뿐입니다.\n"
        "**절대 금지:** '국내도서'만 보고 한국어 원서·한국을 원서 국가로 판정.\n\n"
        "### 규칙 B. 외국인 이름 음차 — bio 부재여도 한국어 원서로 보지 말 것\n"
        "authors[].name이 외국 인명의 한글 음차이면 한국어 원서 판정 **절대 금지**.\n"
        "  · 전형적 한국 성씨(김·이·박·최·정·강·조·윤·장·임)만 있는 이름이 아니면 외국인으로 간주.\n"
        "  · bio 부재를 이유로 한국어 기본값 **금지**.\n"
        "  · ★ 예외 — 역자(번역가) 정보가 **없고**, 저자 이름이 '루하'·'은유'·'하재연' 등\n"
        "    성씨 없이 2~3글자의 순한글로만 이루어진 필명으로 보일 경우,\n"
        "    외국인으로 단정하지 말고 한국인 필명(kor) 가능성을 최우선으로 고려할 것.\n"
        "    역자 없음 + 한글 필명 = 국내 저자 kor로 판정하거나 최소 und로 보류.\n\n"
        "### 규칙 H. 역자 부재 시 기본값 제한\n"
        "translators 배열이 비어 있거나 역자 정보가 전혀 없는 경우,\n"
        "단서 부족을 이유로 무작정 '영어(eng)'를 기본값으로 출력하는 것을 **금지**합니다.\n"
        "  · 역자 없음 + 저자가 한국인 필명으로 보임 → kor\n"
        "  · 역자 없음 + 단서 부족 → und (보류)\n"
        "  · 역자 있음 + 단서 부족 → eng 기본값 허용\n\n"
        "  ★ 역자 없음 + 저자 이름이 외국식(일본식·중국식 등)이어도 함부로 외국어 원서로 단정 금지.\n"
        "    외국식 이름의 저자가 귀화 한국인이거나 한국에서 활동하며 한국어로 집필하는 경우가 있습니다.\n"
        "    역자가 없다는 사실 자체가 '번역서가 아닐 가능성'을 강하게 시사합니다.\n"
        "    bio·출판사·카테고리 등 다른 단서 없이 이름만 보고 외국어 원서로 판정하는 것은 오판입니다.\n"
        "    역자 없음 + 외국식 이름 + 추가 단서 없음 → und (보류)\n"
        "    역자 없음 + 외국식 이름 + bio에 한국 활동 명확 → kor 우선 고려\n\n"
        "### 규칙 D. 도서 제목의 결정적 고유명사 최우선 적용\n"
        "title·description에 특정 국가·문화권을 명확히 지시하는 고유명사가 있으면 즉시 판정.\n"
        "  · 일본: 지브리·라퓨타·토토로·미야자키 등 → jpn\n"
        "  · 미국: 마블·디즈니·픽사·스타워즈 등 → eng\n\n"
        "### 규칙 C. 저자 단서 부실 시 번역가 폴백 (규칙 D 이후)\n"
        "author_signal_confidence=low이고 규칙 D 미해당 시:\n"
        "  · translators[].univ_major_regex.inferred_language 적극 수용\n"
        "    (예: 불어과 역자 → 프랑스어, 노어과 역자 → 러시아어)\n\n"
        "### 규칙 E. 한국계·해외파 저자\n"
        "bio_excerpt에 Stanford·Harvard·Forbes·NYT 등 영미권 기관·언론이 주축이면 해당 언어로 판정.\n\n"
        "### 규칙 G. 역자 국적으로 인한 궤변 절대 금지\n"
        "한국인 번역가가 번역했다는 사실은 원서 언어 추론에 **무관**합니다.\n"
        "  · 호메로스·아리스토텔레스 → 그리스어(gre) / 키케로·베르길리우스 → 라틴어(lat)\n"
        "  · '역자가 한국인이므로 원서를 단정할 수 없다'는 논리 **절대 금지**.\n\n"
        "══════════════════════════════════════════════════════\n"
        "## 추론 우선순위\n"
        "══════════════════════════════════════════════════════\n"
        "0순위 — 역자 유무 확인 (가장 먼저)\n"
        "  · 역자 없음 → 번역서가 아닐 가능성 높음. 이름이 외국식이어도 섣불리 외국어 판정 금지.\n"
        "  · 역자 있음 → 번역서로 간주하고 아래 순위 적용.\n"
        "1순위 — 저자(name, bio_excerpt, univ_major_regex)\n"
        "2순위 — 도서 메타(title, description, original_title) — 규칙 D\n"
        "3순위 — 번역가(univ_major_regex) — 규칙 C 조건에서만\n\n"
        "## author_signal_confidence\n"
        "- high: bio에 결정적 맥락, 또는 규칙 D 고유명사로 확정\n"
        "- medium: bio 일부 단서 있음\n"
        "- low: bio 없음/무의미 → 규칙 D → 규칙 C 순서 적용\n\n"
        "## reasoning_process (한국어)\n"
        "① 분석 맥락 → ② 저자(name·bio) → ③ 규칙 G(역자 국적 궤변 차단) "
        "→ ④ 규칙 D(title) → ⑤ 규칙 C(번역가 전공) → ⑥ 최종 결론\n\n"
        "반드시 JSON 객체 하나만 반환하세요. 키:\n"
        '- reasoning_process (string, 한국어)\n'
        '- author_signal_confidence ("high"|"medium"|"low")\n'
        '- inferred_language (string, 한국어 표기: 영어·프랑스어·그리스어·덴마크어 등)\n'
        '  ★ 절대 금지: "판별 불가"·"불명"·"알 수 없음" 등 미판정 표현.\n'
        '  단서 부족 시 기본값 규칙:\n'
        '    - 역자(번역가)가 명확히 존재하는 번역서 → 영어(eng) 기본값 허용\n'
        '    - 역자 없음 + 저자가 한글 필명(2~3글자 순한글)으로 보임 → 한국어(kor)\n'
        '    - 역자 없음 + 그 외 단서 부족 → 반드시 und 사용. 영어 기본값 금지.\n'
        '- inferred_country  (string, 한국어 표기: 미국·프랑스·일본 등)\n'
        '- is_indirect_translation (boolean)\n'
    )

    def gpt_nonfiction_payload(
        self,
        item: Dict,
        original_title: str,
        author_bio: str,
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

        authors_info    = [self._build_author_info(n, author_bio if i == 0 else "")
                           for i, n in enumerate(writer_names[:2])]
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
            result = {
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
            # CHAR_LANG_MAP 기반 특수문자 보정 (언어 전용 마커만 포함)
            for chars, lang in LangFieldBuilder.CHAR_LANG_MAP:
                if any(ch in text for ch in chars):
                    return lang
            # 이탈리아어 전형 악센트(à·è·ì·ò·ù) — 다른 언어와 겹치므로
            # CHAR_LANG_MAP 체크를 모두 통과한 뒤에만 이탈리아어로 유추
            if re.search(r"[àèìòù]", text):
                return "ita"
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
        label: str = "GPT-General",
    ) -> Optional[str]:
        """
        2단계: GPT 일반 판정 (제목·카테고리·출판사·저자·원제 종합)
        결과가 ALLOWED_CODES에 없으면 None 반환.
        """
        code = self.gpt_guess_original_lang(
            title, category_text, publisher, author, original_title,
            author_bio=author_bio, translator_bio=translator_bio,
            has_translator=has_translator,
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
        label: str = "Author-Hint",
    ) -> Optional[str]:
        """
        3단계: 저자 기반 GPT 판정
        결과가 ALLOWED_CODES에 없으면 None 반환.
        역자가 있는 경우 kor 반환을 신뢰하지 않음.
        """
        if not author:
            return None
        code = self.gpt_guess_original_lang_by_author(
            author, title, category_text, publisher,
            author_bio=author_bio, translator_bio=translator_bio,
            has_translator=has_translator,
        )
        # 역자가 있는데 GPT가 kor을 반환하면 신뢰하지 않음
        if has_translator and code == "kor":
            self._dbg(f"📘 [{label}] 역자 있음 + kor 반환 → 신뢰 불가, und 처리")
            return None
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
            _is_latin_only = (
                bool(original_title)
                and _RE_LATIN.search(original_title)
                and not _RE_NON_LATIN.search(original_title)
            )
            if _is_latin_only:
                self._dbg(f"📘 [1.5단계] 라틴 원제 GPT 판별 시작: '{original_title}'")
                title_lang = self.gpt_guess_from_original_title_only(original_title)
                if title_lang and title_lang != "und":
                    self._dbg(
                        f"📘 [1.5단계/원제GPT] '{original_title}' → "
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
                    "비라틴 문자 포함 → 스킵, 2단계로 진행"
                )
            else:
                self._dbg("📘 [1.5단계] 원제 없음 → 스킵, 2단계로 진행")

            # ══════════════════════════════════════════════════
            # 2단계: 저자/역자 Bio 크롤링 → GPT 단일 호출
            # ══════════════════════════════════════════════════
            author_bio = translator_bio = ""
            self._dbg("📘 [2단계] Bio 수집 시작…")
            try:
                author_bio, translator_bio = self._scraper.fetch_bios(_item)
                if author_bio:
                    self._dbg(f"📘 [Bio] 저자 Bio {len(author_bio)}자")
                if translator_bio:
                    self._dbg(f"📘 [Bio] 역자 Bio {len(translator_bio)}자")
                if not author_bio and not translator_bio:
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
                author_bio=author_bio,
                translator_bio=translator_bio,
                translator_name=translator_name_for_payload,
                author_name=_author_name_for_payload,
            )

            if llm_result:
                lang_name = llm_result.get("inferred_language", "")
                isds = _resolve_lang_name_to_isds(lang_name) if lang_name else None
                if isds and isds in ALLOWED_CODES:
                    self._dbg(f"📘 [2단계/GPT] 확정: {lang_name} → {isds}")
                    return isds
                self._dbg(f"📘 [2단계/GPT] 미확정 (inferred_language='{lang_name}')")

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
        self._dbg("📘 [Pipeline] 문학: Rule-based → GPT-General → Author-Hint")
        pipeline = [
            lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
            lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, has_translator=has_translator, label="GPT-General"),
            lambda: self._try_gpt_author(author, title, category_text, publisher, has_translator=has_translator, label="Author-Hint"),
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

            # ── 태그 조합 ──────────────────────────────────────
            # 역자 있는데 lang_h == lang_a → GPT 오판 보정
            if has_translator and lang_h == lang_a and lang_h != "und":
                self._dbg(
                    f"📘 [보정] 역자 있음 + lang_h({lang_h})==lang_a({lang_a})"
                    " → 원서 언어 미확정(und)으로 처리"
                )
                lang_h = "und"

            # ── 태그 조합 ──────────────────────────────────────
            has_h = lang_h and lang_h != lang_a and lang_h != "und"
            if has_h:
                tag_041 = f"041 $a{lang_a} $h{lang_h}"
            else:
                tag_041 = f"041 $a{lang_a}"

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
