"""
lang_field.py
─────────────────────────────────────────────────────────────────────────────
KORMARC 041(언어코드) · 546(언어주기) 필드 생성 모듈 (하이브리드 비문학 최적화 버전)

【포함 기능】
  - 기존 문학 파이프라인 (규칙 -> GPT -> 저자) 유지
  - [NEW] 비문학 하이브리드 파이프라인 (Fast Track: 저자 단서 -> Safe Track: 역자 커리어 폴백)
  - 속도 저하의 주범인 ItemSearch(50권 조회)를 저자 단서가 부족할 때만 선택적 가동
"""

from __future__ import annotations

import re
import html
import time
from collections import defaultdict
from typing import Callable, Optional, Dict, Any, List

try:
    import requests
    from bs4 import BeautifulSoup
    _SCRAPER_AVAILABLE = True
except ImportError:
    _SCRAPER_AVAILABLE = False


# ═══════════════════════════════════════════════════════════════
# 1. 상수 및 하이브리드 분석 유틸리티
# ═══════════════════════════════════════════════════════════════

ISDS_LANGUAGE_CODES: dict[str, str] = {
    'kor': '한국어', 'eng': '영어',  'jpn': '일본어',   'chi': '중국어',
    'rus': '러시아어', 'ara': '아랍어', 'fre': '프랑스어', 'ger': '독일어',
    'ita': '이탈리아어', 'spa': '스페인어', 'por': '포르투갈어', 'tur': '터키어',
    'und': '알 수 없음',
}

ALLOWED_CODES: frozenset[str] = frozenset(ISDS_LANGUAGE_CODES.keys()) - {"und"}

# --- 문자 체계 정규식 (Fast Track용) ---
RE_KANA = re.compile(r"[\u3040-\u309F\u30A0-\u30FF]")
RE_HAN = re.compile(r"[\u4E00-\u9FFF]")
RE_LATIN = re.compile(r"[A-Za-z]")

# --- 전공 -> 언어 매핑 (Fast Track용) ---
_MAJOR_LANG_RULES: list[tuple[str, str]] = [
    (r"노어|러시아|슬라브", "러시아어"),
    (r"영미|영어|미국문학|영문", "영어"),
    (r"불어|프랑스", "프랑스어"),
    (r"독어|독일", "독일어"),
    (r"스페인|스페인어|히스패닉", "스페인어"),
    (r"이탈리아|이태리", "이탈리아어"),
    (r"일본|일어", "일본어"),
    (r"중국|중문|한문|중어", "중국어"),
]

def _script_weights_on_text(text: str) -> dict[str, float]:
    """문자 체계 기반 가중치 계산"""
    w: dict[str, float] = defaultdict(float)
    if not text:
        return dict(w)
    if RE_KANA.search(text): w["원제_가나(일본어)"] += 2.0
    if RE_HAN.search(text): w["원제_한자(중국/일본어)"] += 1.0
    if RE_LATIN.search(text): w["원제_라틴(영미/유럽권)"] += 1.5
    return dict(w)

def extract_univ_major_regex(text: str) -> Optional[dict[str, Optional[str]]]:
    """소개글에서 출신 대학 및 전공을 추출하고 주력 언어 추론"""
    if not text or not text.strip():
        return None
    m = re.search(r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*([가-힣A-Za-z·\s]{2,20}(?:학과|전공|학부))", text)
    if not m:
        m = re.search(r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*에서\s*([가-힣A-Za-z·\s]{2,20}(?:학과|전공|학부))", text)
    if not m:
        return None
    uni, maj = m.group(1).strip(), m.group(2).strip()
    
    inferred_lang = None
    for pat, lang in _MAJOR_LANG_RULES:
        if re.search(pat, maj, re.I):
            inferred_lang = lang
            break
            
    return {"university": uni, "major": maj, "inferred_language": inferred_lang}


# ═══════════════════════════════════════════════════════════════
# 2. AladinAuthorScraper
# ═══════════════════════════════════════════════════════════════

class AladinAuthorScraper:
    _DETAIL_BASE    = "https://www.aladin.co.kr/shop/wproduct.aspx"
    _OVERVIEW_BASE  = "https://www.aladin.co.kr/author/wauthor_overview.aspx"
    _HEADERS: dict[str, str] = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/124.0.0.0 Safari/537.36"
        ),
        "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8",
        "Referer": "https://www.aladin.co.kr/",
    }
    _TIMEOUT    = 10
    _RETRY      = 2
    _RETRY_WAIT = 1.0

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

    def extract_author_ids(self, item_id: str, *, want_author: bool = True, want_translator: bool = True) -> dict[str, list[str]]:
        result: dict[str, list[str]] = {"author": [], "translator": []}
        if not _SCRAPER_AVAILABLE or not item_id:
            return result

        resp = self._get(self._DETAIL_BASE, params={"ItemId": item_id})
        if resp is None:
            return result

        soup = BeautifulSoup(resp.text, "html.parser")
        author_pattern = re.compile(r"AuthorSearch=(?:[^&]*?@)?(\d+)", re.I)
        translator_markers = re.compile(r"(옮긴이|역자|번역|옮김|역)", re.I)

        seen: set[str] = set()
        for a_tag in soup.find_all("a", href=True):
            href = a_tag.get("href", "")
            m = author_pattern.search(href)
            if not m:
                continue

            aid = m.group(1)
            if aid in seen:
                continue
            seen.add(aid)

            context = ""
            parent = a_tag.parent
            if parent:
                context = parent.get_text(" ", strip=True)

            if translator_markers.search(context):
                if want_translator: result["translator"].append(aid)
            else:
                if want_author: result["author"].append(aid)

        return result

    def scrape_author_bio_from_overview(self, author_id: str) -> str:
        if not _SCRAPER_AVAILABLE or not author_id:
            return ""

        resp = self._get(self._OVERVIEW_BASE, params={"AuthorSearch": f"@{author_id}"})
        if resp is None:
            return ""

        soup = BeautifulSoup(resp.text, "html.parser")
        decompose_tags = ("script", "style", "meta", "noscript", "header", "footer", "nav", "aside", "menu", "form", "button", "iframe", "ul", "ol", "li", "a")
        for tag_name in decompose_tags:
            for element in soup.find_all(tag_name):
                element.decompose()

        root = soup
        for attr in ("id", "class"):
            found = soup.find(attrs={attr: re.compile(r"author|writer|profile|bio|intro", re.I)})
            if found:
                root = found
                break

        chunks: list[str] = []
        for p in root.find_all("p"):
            text = p.get_text(separator=" ", strip=True)
            if len(text) >= 8: chunks.append(text)

        for div in root.find_all("div"):
            if div.find(["div", "p", "ul", "ol", "nav", "table"]): continue
            text = div.get_text(separator=" ", strip=True)
            if len(text) >= 20: chunks.append(text)

        bio_text = "\n\n".join(dict.fromkeys(chunks))
        return bio_text[:1500] if bio_text else ""

    def fetch_bios(self, item_id: str) -> tuple[str, str]:
        if not _SCRAPER_AVAILABLE or not item_id:
            return "", ""
        ids = self.extract_author_ids(item_id)
        author_bio = self.scrape_author_bio_from_overview(ids["author"][0]) if ids["author"] else ""
        translator_bio = self.scrape_author_bio_from_overview(ids["translator"][0]) if ids["translator"] else ""
        return author_bio, translator_bio
        
    def fetch_translator_career(self, translator_name: str, ttbkey: str, max_results: int = 50) -> list[dict]:
        """역자 커리어 조회를 위한 ItemSearch 폴백 (API 호출 병목 구간)"""
        if not _SCRAPER_AVAILABLE or not translator_name or not ttbkey:
            return []
            
        SEARCH_URL = "http://www.aladin.co.kr/ttb/api/ItemSearch.aspx"
        params = {
            "ttbkey": ttbkey.strip(),
            "QueryType": "Author",
            "Query": translator_name.strip(),
            "MaxResults": str(max_results),
            "start": "1",
            "SearchTarget": "Book",
            "output": "js",
            "Version": "20131101",
            "OptResult": "authors",
        }
        resp = self._get(SEARCH_URL, params=params)
        if resp:
            try:
                return resp.json().get("item", [])
            except Exception:
                pass
        return []


# ═══════════════════════════════════════════════════════════════
# 3. LangFieldBuilder
# ═══════════════════════════════════════════════════════════════

class LangFieldBuilder:
    LIT_KEYWORDS: dict[str, list[str]] = {
        "ko": ["문학", "소설", "시", "희곡"],
        "en": ["literature", "fiction", "novel", "poetry", "poem", "drama", "play"],
    }
    NONFICTION_KEYWORDS: dict[str, list[str]] = {
        "ko": ["역사", "근현대사", "서양사", "유럽사", "전기", "평전", "사회", "정치", "철학", "경제", "경영", "인문", "에세이", "수필"],
        "en": ["history", "biography", "memoir", "politics", "philosophy", "economics", "science", "technology", "nonfiction", "essay", "essays"],
    }
    SF_GUARD_KEYWORDS: dict[str, list[str]] = {
        "ko": ["과학", "기술"],
        "en": ["science", "technology"],
    }
    CATEGORY_LANG_MAP: list[tuple[list[str], str]] = [
        (["일본"], "jpn"), (["중국"], "chi"), (["영미", "영어", "아일랜드"], "eng"),
        (["프랑스"], "fre"), (["독일", "오스트리아"], "ger"), (["러시아"], "rus"),
        (["이탈리아"], "ita"), (["스페인"], "spa"), (["포르투갈"], "por"), (["튀르키예", "터키"], "tur"),
    ]
    CHAR_LANG_MAP: list[tuple[str, str]] = [
        ("éèêàçùôâîû", "fre"), ("ñáíóú", "spa"), ("ãõ", "por"),
    ]

    def __init__(
        self,
        openai_client=None,
        model: str = "gpt-4o",
        ttbkey: str = "",  # 역자 검색용 TTB 키 주입
        dbg_fn: Optional[Callable] = None,
        dbg_err_fn: Optional[Callable] = None,
    ):
        self._client  = openai_client
        self._model   = model
        self._ttbkey  = ttbkey
        self._dbg     = dbg_fn or (lambda *a: print("[DBG]", *a))
        self._dbg_err = dbg_err_fn or (lambda *a: print("[ERR]", *a))
        self._scraper = AladinAuthorScraper()

    # ─────────────────────────────────────────────
    # GPT 및 규칙 기반 감지 (기존 기능 유지)
    # ─────────────────────────────────────────────

    def gpt_guess_original_lang(self, title: str, category: str, publisher: str, author: str = "", original_title: str = "", author_bio: str = "", translator_bio: str = "") -> str:
        if not self._client: return "und"
        bio_block = ""
        if author_bio: bio_block += f"\n- 저자 소개글: {author_bio[:400]}"
        prompt = f"""아래 도서의 원서 언어(041 $h)를 ISDS 코드로 추정해줘.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur
- 제목: {title} / 원제: {original_title or "(없음)"} / 분류: {category} / 저자: {author}{bio_block}
출력형식:
$h=[ISDS 코드]
#reason=[근거]"""
        try:
            resp = self._client.chat.completions.create(
                model=self._model, messages=[{"role": "system", "content": "사서용 언어 추정기"}, {"role": "user", "content": prompt}], temperature=0
            )
            code, reason, _ = _extract_code_and_reason(resp.choices[0].message.content, "$h")
            return code if code in ALLOWED_CODES else "und"
        except Exception: return "und"

    def gpt_guess_main_lang(self, title: str, category: str, publisher: str) -> str:
        if not self._client: return "und"
        prompt = f"""본문 언어(041 $a)를 ISDS 코드로 추정.
- 제목: {title} / 분류: {category} / 출판사: {publisher}
출력형식:
$a=[ISDS 코드]"""
        try:
            resp = self._client.chat.completions.create(
                model=self._model, messages=[{"role": "system", "content": "사서용 본문 언어 추정기"}, {"role": "user", "content": prompt}], temperature=0
            )
            code, _, _ = _extract_code_and_reason(resp.choices[0].message.content, "$a")
            return code if code in ALLOWED_CODES else "und"
        except Exception: return "und"

    def gpt_guess_original_lang_by_author(self, author: str, title: str = "", category: str = "", publisher: str = "", author_bio: str = "", translator_bio: str = "") -> str:
        if not self._client: return "und"
        bio_block = f"\n- 저자 소개글: {author_bio[:400]}" if author_bio else ""
        prompt = f"""저자 정보를 중심으로 원서 언어(041 $h) 추정.
- 저자: {author} / 제목: {title}{bio_block}
출력형식:
$h=[ISDS 코드]"""
        try:
            resp = self._client.chat.completions.create(
                model=self._model, messages=[{"role": "system", "content": "저자 기반 원서 언어 추정기"}, {"role": "user", "content": prompt}], temperature=0
            )
            code, _, _ = _extract_code_and_reason(resp.choices[0].message.content, "$h")
            return code if code in ALLOWED_CODES else "und"
        except Exception: return "und"

    @staticmethod
    def detect_language_by_unicode(text: str) -> str:
        text = re.sub(r'[\s\W_]+', '', text or "")
        if not text: return 'und'
        c = text[0]
        if '\uac00' <= c <= '\ud7a3': return 'kor'
        if '\u3040' <= c <= '\u30ff': return 'jpn'
        if '\u4e00' <= c <= '\u9fff': return 'chi'
        return 'und'

    @staticmethod
    def override_language_by_keywords(text: str, initial_lang: str) -> str:
        text = (text or "").lower()
        if initial_lang == 'chi' and re.search(r'[\u3040-\u30ff]', text): return 'jpn'
        if initial_lang in ('und', 'eng'):
            if "spanish" in text or "español" in text: return "spa"
            if "french" in text or "français" in text: return "fre"
            if "german" in text or "deutsch" in text: return "ger"
            for chars, lang in LangFieldBuilder.CHAR_LANG_MAP:
                if any(ch in text for ch in chars): return lang
        return initial_lang

    def detect_language(self, text: str) -> str:
        return self.override_language_by_keywords(text, self.detect_language_by_unicode(text))

    @staticmethod
    def tokenize_category(text: str) -> list[str]:
        if not text: return []
        raw = re.split(r'[>/\s]+', re.sub(r'[()]+', ' ', text))
        tokens = [w for w in raw if w.strip()]
        return tokens + [w.lower() for w in tokens]

    @staticmethod
    def _has_kw(tokens: list[str], kws: list[str]) -> bool:
        return any(k in set(tokens) for k in kws)

    @staticmethod
    def _trigger_kw(tokens: list[str], kws: list[str]) -> Optional[str]:
        s = set(tokens)
        return next((k for k in kws if k in s), None)

    def is_literature_category(self, category_text: str) -> bool:
        tokens = self.tokenize_category(category_text or "")
        return self._has_kw(tokens, self.LIT_KEYWORDS["ko"]) or self._has_kw(tokens, self.LIT_KEYWORDS["en"])

    def is_nonfiction_override(self, category_text: str) -> bool:
        tokens  = self.tokenize_category(category_text or "")
        lit_top = "소설/시/희곡" in (category_text or "")
        if self._trigger_kw(tokens, self.NONFICTION_KEYWORDS["ko"]) or self._trigger_kw(tokens, self.NONFICTION_KEYWORDS["en"]):
            return True
        if not lit_top and (self._trigger_kw(tokens, self.SF_GUARD_KEYWORDS["ko"]) or self._trigger_kw(tokens, self.SF_GUARD_KEYWORDS["en"])):
            return True
        return False

    @staticmethod
    def is_domestic_category(category_text: str) -> bool:
        return "국내도서" in (category_text or "")

    def reconcile_language(self, candidate: str, fallback_hint: Optional[str] = None, author_hint: Optional[str] = None) -> str:
        if author_hint and author_hint != "und" and author_hint != candidate: return author_hint
        if fallback_hint and fallback_hint != "und" and fallback_hint != candidate:
            if candidate in {"ita", "fre", "spa", "por"} and fallback_hint == "eng": return candidate
            return fallback_hint
        return candidate

    # ─────────────────────────────────────────────
    # 파이프라인 단계 정의
    # ─────────────────────────────────────────────

    def _try_rule(self, subject_lang: str, rule_from_original: str, label: str = "Rule-based") -> Optional[str]:
        result = subject_lang or rule_from_original or None
        if result and result != "und":
            self._dbg(f"📘 [{label}] 확정: {result}")
            return result
        return None

    def _try_gpt_general(self, title: str, category_text: str, publisher: str, author: str, original_title: str, label: str = "GPT-General") -> Optional[str]:
        code = self.gpt_guess_original_lang(title, category_text, publisher, author, original_title)
        return code if code and code != "und" and code in ALLOWED_CODES else None

    def _try_gpt_author(self, author: str, title: str, category_text: str, publisher: str, label: str = "Author-Hint") -> Optional[str]:
        if not author: return None
        code = self.gpt_guess_original_lang_by_author(author, title, category_text, publisher)
        return code if code and code != "und" and code in ALLOWED_CODES else None

    def _try_hybrid_nonfiction_pipeline(
        self, title: str, category_text: str, publisher: str, author: str, translator: str,
        original_title: str, author_bio: str, translator_bio: str, label: str = "Hybrid-Nonfiction"
    ) -> Optional[str]:
        """Fast Track(저자 단서) 평가 후 부족 시 Safe Track(역자 커리어 폴백) 가동"""
        if not self._client: return None

        # 1. Fast Track (저자 단서 분석 - API 호출 없음)
        author_script_weights = _script_weights_on_text(f"{title} {original_title} {author_bio[:500]}")
        author_major_info = extract_univ_major_regex(author_bio)
        
        author_confidence = "low"
        if author_major_info and author_major_info.get("inferred_language"):
            author_confidence = "high"
            self._dbg(f"⚡ [Fast Track] 저자 전공 단서 발견: {author_major_info['inferred_language']}")
        elif sum(author_script_weights.values()) >= 2.0:
            author_confidence = "medium"
            self._dbg(f"⚡ [Fast Track] 도서/저자 문자 가중치 유의미: {author_script_weights}")

        # 2. Safe Track (역자 폴백 - 저자 단서가 부족할 때만 가동!)
        translator_major_info = None
        translator_career_summary = ""
        if author_confidence == "low" and (translator_bio or translator):
            self._dbg("🛡️ [Safe Track] 저자 단서 부족. 역자 폴백 가동...")
            if translator_bio:
                translator_major_info = extract_univ_major_regex(translator_bio)
            if translator and self._ttbkey:
                career_items = self._scraper.fetch_translator_career(translator, self._ttbkey)
                if career_items:
                    valid_careers = [b for b in career_items if b.get('categoryName', '').split('>')[0] in category_text]
                    translator_career_summary = f"({len(valid_careers)}권 번역 이력 발견)"

        # 3. GPT 프롬프트 주입
        prompt = f"""아래 도서의 원서 언어(041 $h)를 ISDS 코드로 추정해.
가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

[도서 기본]
- 제목: {title} / 원제: {original_title or "(없음)"} / 분류: {category_text}

[1순위: 저자(Fast Track) 분석 결과]
- 저자명: {author}
- 저자 전공 추출: {author_major_info}
- 저자/도서 문자 가중치: {author_script_weights}
- 저자 소개글: {author_bio[:400]}

[2순위: 역자(Safe Track) 분석 결과 (저자 정보 부족시 참고)]
- 역자명: {translator}
- 역자 전공 추출: {translator_major_info}
- 역자 커리어 요약: {translator_career_summary if translator_career_summary else '(분석 안함)'}
- 역자 소개글: {translator_bio[:400]}

[지침]
1. 1순위 저자의 전공(inferred_language)이나 문자 가중치가 뚜렷하면 최우선으로 적용.
2. 저자 정보가 부실하거나 외국인 이름 음차라면 2순위 역자의 전공 및 커리어(중역 의심)를 적극 수용.
3. '국내도서'라는 이유만으로 한국어로 판정 금지.

출력형식:
$h=[ISDS 코드]
#reason=[어느 Track을 우선했는지 요약]"""

        try:
            resp = self._client.chat.completions.create(
                model=self._model, messages=[{"role": "system", "content": "사서용 비문학 하이브리드 추정기"}, {"role": "user", "content": prompt}], temperature=0
            )
            content = (resp.choices[0].message.content or "").strip()
            code, reason, _ = _extract_code_and_reason(content, "$h")
            if code in ALLOWED_CODES:
                self._dbg(f"📘 [{label}] 확정: {code} (사유: {reason})")
                return code
            return None
        except Exception as e:
            self._dbg_err(f"GPT 하이브리드 오류: {e}")
            return None

    def determine_h_language(self, title: str, original_title: str, category_text: str, publisher: str, author: str, translator: str, subject_lang: str, item_id: str = "") -> str:
        lit_raw = self.is_literature_category(category_text)
        nf_override = self.is_nonfiction_override(category_text)
        is_lit = lit_raw and not nf_override

        rule_from_original = self.detect_language(original_title) if original_title else "und"
        fallback_hint = subject_lang or rule_from_original or None

        author_bio, translator_bio = "", ""
        if not is_lit and item_id:
            try:
                author_bio, translator_bio = self._scraper.fetch_bios(item_id)
            except Exception as e:
                self._dbg_err(f"Bio 크롤링 오류: {e}")

        if is_lit:
            self._dbg("📘 [Pipeline] 문학 파이프라인 시작: Rule-based → GPT-General → Author-Hint")
            pipeline = [
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
                lambda: self._try_gpt_general(title, category_text, publisher, author, original_title, label="GPT-General"),
                lambda: self._try_gpt_author(author, title, category_text, publisher, label="Author-Hint"),
            ]
        else:
            self._dbg("📘 [Pipeline] 비문학 파이프라인 시작: Hybrid(Fast+Safe Track) 단일 호출 → Rule-based")
            pipeline = [
                lambda: self._try_hybrid_nonfiction_pipeline(
                    title, category_text, publisher, author, translator, original_title, 
                    author_bio=author_bio, translator_bio=translator_bio
                ),
                lambda: self._try_rule(subject_lang, rule_from_original, "Rule-based"),
            ]

        lang_h, author_hint = None, None
        for i, step in enumerate(pipeline):
            result = step()
            if result:
                if is_lit and i == len(pipeline) - 1: author_hint = result
                else:
                    lang_h = result
                    break

        lang_h = self.reconcile_language(candidate=lang_h or "und", fallback_hint=fallback_hint, author_hint=author_hint)
        return lang_h if lang_h in ALLOWED_CODES else "und"

    # ─────────────────────────────────────────────
    # 최종 KORMARC 태그 및 기타 헬퍼
    # ─────────────────────────────────────────────

    def _extract_translator_name(self, item: dict) -> str:
        """item 딕셔너리에서 역자 이름 추출 유틸"""
        authors_list = (item.get("subInfo") or {}).get("authors") or []
        for auth in authors_list:
            if not isinstance(auth, dict): continue
            role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "")
            if any(m in role for m in ("옮긴이", "역자", "옮김", "번역")):
                return (auth.get("authorName") or "").strip()
        
        raw_author = item.get("author", "")
        for part in raw_author.split(","):
            if any(k in part for k in ["옮긴이", "역자", "옮김", "번역"]):
                return re.sub(r"\(.*?\)|옮긴이|역자|옮김|지은이|지음|역", "", part, flags=re.I).strip()
        return ""

    def get_kormarc_tags(self, item: dict, detail: dict) -> tuple[Optional[str], Optional[str], str]:
        item, detail = item or {}, detail or {}
        title = item.get("title", "") or ""
        publisher = item.get("publisher", "") or ""
        author = item.get("author", "") or ""
        translator = self._extract_translator_name(item)
        item_id = str(item.get("itemId", "") or "")

        subinfo = (item.get("subInfo") or {}) or {}
        original_title = html.unescape(subinfo.get("originalTitle", "") or "")
        if not original_title: original_title = detail.get("original_title", "") or ""

        subject_lang = detail.get("subject_lang")
        category_text = item.get("categoryText", "") or detail.get("category_text", "") or ""

        try:
            lang_a = self.detect_language(title)
            if self.is_domestic_category(category_text): lang_a = "kor"
            if lang_a in ("und", "eng"):
                gpt_a = self.gpt_guess_main_lang(title, category_text, publisher)
                lang_a = gpt_a if gpt_a in ALLOWED_CODES else "und"

            lang_h = self.determine_h_language(
                title=title, original_title=original_title, category_text=category_text,
                publisher=publisher, author=author, translator=translator,
                subject_lang=subject_lang or "", item_id=item_id
            )

            tag_041 = f"041 $a{lang_a} $h{lang_h}" if lang_h and lang_h != lang_a and lang_h != "und" else f"041 $a{lang_a}"

            if "$h" not in tag_041: return None, None, original_title
            return tag_041, self.generate_546_from_041(tag_041), original_title

        except Exception as e:
            return f"📕 예외 발생: {e}", "", original_title

    @staticmethod
    def generate_546_from_041(marc_041: str) -> str:
        a_codes, h_code = [], None
        for part in marc_041.split():
            if part.startswith("$a"): a_codes.append(part[2:])
            elif part.startswith("$h"): h_code = part[2:]
        if len(a_codes) == 1:
            a_lang = ISDS_LANGUAGE_CODES.get(a_codes[0], "알 수 없음")
            if h_code: return f"{ISDS_LANGUAGE_CODES.get(h_code, '알 수 없음')} 원작을 {a_lang}로 번역"
            return f"{a_lang}로 씀"
        if len(a_codes) > 1: return f"{'、'.join([ISDS_LANGUAGE_CODES.get(c, '알 수 없음') for c in a_codes])} 병기"
        return "언어 정보 없음"

def _extract_code_and_reason(content: str, code_key: str = "$h") -> tuple[str, str, str]:
    code = reason = signals = ""
    for ln in [l.strip() for l in (content or "").splitlines() if l.strip()]:
        if ln.startswith(f"{code_key}="): code = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#reason="): reason = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#signals="): signals = ln.split("=", 1)[1].strip()
    return code or "und", reason, signals

def generate_546_from_041_kormarc(marc_041: str) -> str:
    return LangFieldBuilder.generate_546_from_041(marc_041)
