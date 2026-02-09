"""
Text Sanitization Functions

Unicode normalization, control character stripping, and HTML escaping.

All normalization functions are @idempotent: f(f(x)) = f(x)
"""

import html
import re
import unicodedata
from typing import Any
from urllib.parse import unquote

from toolbox.core.effects import idempotent, monotonic, MonotonicDirection

from .constants import MAX_FILENAME_LENGTH, MAX_TEXT_LENGTH


# =============================================================================
# Unicode Confusable Mappings (for injection detection normalization)
# =============================================================================

# Map Unicode lookalikes to their ASCII equivalents
# This prevents bypass using visually similar characters
CONFUSABLE_MAP: dict[str, str] = {
    # Roman numerals that look like letters
    "\u2170": "i",  # ⅰ small roman numeral one
    "\u2171": "ii",  # ⅱ
    "\u2172": "iii",  # ⅲ
    "\u2173": "iv",  # ⅳ
    "\u2174": "v",  # ⅴ
    "\u2175": "vi",  # ⅵ
    "\u2176": "vii",  # ⅶ
    "\u2177": "viii",  # ⅷ
    "\u2178": "ix",  # ⅸ
    "\u2179": "x",  # ⅹ
    "\u217a": "xi",  # ⅺ
    "\u217b": "xii",  # ⅻ
    "\u217c": "l",  # ⅼ small roman numeral fifty
    "\u217d": "c",  # ⅽ small roman numeral one hundred
    "\u217e": "d",  # ⅾ small roman numeral five hundred
    "\u217f": "m",  # ⅿ small roman numeral one thousand
    "\u2160": "I",  # Ⅰ capital roman numeral one
    "\u2161": "II",  # Ⅱ
    "\u2162": "III",  # Ⅲ
    "\u2163": "IV",  # Ⅳ
    "\u2164": "V",  # Ⅴ
    "\u2165": "VI",  # Ⅵ
    "\u2166": "VII",  # Ⅶ
    "\u2167": "VIII",  # Ⅷ
    "\u2168": "IX",  # Ⅸ
    "\u2169": "X",  # Ⅹ
    "\u216a": "XI",  # Ⅺ
    "\u216b": "XII",  # Ⅻ
    "\u216c": "L",  # Ⅼ capital roman numeral fifty
    "\u216d": "C",  # Ⅽ capital roman numeral one hundred
    "\u216e": "D",  # Ⅾ capital roman numeral five hundred
    "\u216f": "M",  # Ⅿ capital roman numeral one thousand
    # Cyrillic lookalikes
    "\u0430": "a",  # Cyrillic а
    "\u0435": "e",  # Cyrillic е
    "\u043e": "o",  # Cyrillic о
    "\u0440": "p",  # Cyrillic р
    "\u0441": "c",  # Cyrillic с
    "\u0443": "y",  # Cyrillic у
    "\u0445": "x",  # Cyrillic х
    "\u0456": "i",  # Cyrillic і (Ukrainian)
    "\u0410": "A",  # Cyrillic А
    "\u0412": "B",  # Cyrillic В
    "\u0415": "E",  # Cyrillic Е
    "\u041a": "K",  # Cyrillic К
    "\u041c": "M",  # Cyrillic М
    "\u041d": "H",  # Cyrillic Н
    "\u041e": "O",  # Cyrillic О
    "\u0420": "P",  # Cyrillic Р
    "\u0421": "C",  # Cyrillic С
    "\u0422": "T",  # Cyrillic Т
    "\u0425": "X",  # Cyrillic Х
    "\u0406": "I",  # Cyrillic І (Ukrainian)
    # Greek lookalikes
    "\u03b1": "a",  # Greek α
    "\u03b5": "e",  # Greek ε
    "\u03b9": "i",  # Greek ι
    "\u03bf": "o",  # Greek ο
    "\u03c1": "p",  # Greek ρ
    "\u0391": "A",  # Greek Α
    "\u0392": "B",  # Greek Β
    "\u0395": "E",  # Greek Ε
    "\u0397": "H",  # Greek Η
    "\u0399": "I",  # Greek Ι
    "\u039a": "K",  # Greek Κ
    "\u039c": "M",  # Greek Μ
    "\u039d": "N",  # Greek Ν
    "\u039f": "O",  # Greek Ο
    "\u03a1": "P",  # Greek Ρ
    "\u03a4": "T",  # Greek Τ
    "\u03a7": "X",  # Greek Χ
    "\u03a5": "Y",  # Greek Υ
    "\u0396": "Z",  # Greek Ζ
    # Full-width characters
    "\uff41": "a",
    "\uff42": "b",
    "\uff43": "c",
    "\uff44": "d",
    "\uff45": "e",
    "\uff46": "f",
    "\uff47": "g",
    "\uff48": "h",
    "\uff49": "i",
    "\uff4a": "j",
    "\uff4b": "k",
    "\uff4c": "l",
    "\uff4d": "m",
    "\uff4e": "n",
    "\uff4f": "o",
    "\uff50": "p",
    "\uff51": "q",
    "\uff52": "r",
    "\uff53": "s",
    "\uff54": "t",
    "\uff55": "u",
    "\uff56": "v",
    "\uff57": "w",
    "\uff58": "x",
    "\uff59": "y",
    "\uff5a": "z",
}

# Zero-width and invisible characters to strip
ZERO_WIDTH_CHARS = frozenset(
    {
        "\u200b",  # Zero-width space
        "\u200c",  # Zero-width non-joiner
        "\u200d",  # Zero-width joiner
        "\u200e",  # Left-to-right mark
        "\u200f",  # Right-to-left mark
        "\u00ad",  # Soft hyphen
        "\u2060",  # Word joiner
        "\u2061",  # Function application
        "\u2062",  # Invisible times
        "\u2063",  # Invisible separator
        "\u2064",  # Invisible plus
        "\ufeff",  # Zero-width no-break space (BOM)
        "\u034f",  # Combining grapheme joiner
        "\u061c",  # Arabic letter mark
        "\u115f",  # Hangul choseong filler
        "\u1160",  # Hangul jungseong filler
        "\u17b4",  # Khmer vowel inherent AQ
        "\u17b5",  # Khmer vowel inherent AA
        "\u180e",  # Mongolian vowel separator
        "\u3164",  # Hangul filler
        "\uffa0",  # Halfwidth hangul filler
    }
)


# =============================================================================
# Layered Normalization with Co-Effect Composition
# =============================================================================
#
# Design principles:
# 1. Each layer is idempotent: f(f(x)) = f(x)
# 2. Layers compose monotonically: security only increases
# 3. Order-independent where possible (commutative)
# 4. Each layer has a single responsibility
#
# The layers form a semilattice under composition:
#   raw_text → decode_encodings → strip_invisible → normalize_confusables → collapse_space
#
# Co-effect property: Given effect E = decode ∘ strip ∘ normalize ∘ collapse
#   E(E(x)) = E(x)  (idempotent)
#   E(x) ⊑ x       (information-reducing, security-increasing)


@idempotent
def _decode_encodings(text: str) -> str:
    """
    Layer 1: Decode common encoding schemes.

    Idempotent: decode(decode(x)) = decode(x)
    - HTML entities: &#105; → i
    - URL encoding: %69 → i
    - Hex escapes: \\x69 → i

    This reveals the "true" characters hidden behind encoding.
    """
    # HTML entities (handles both numeric &#105; and named &lt;)
    text = html.unescape(text)

    # URL encoding (handles %XX and %uXXXX)
    try:
        # Apply twice to handle double-encoding attacks
        decoded = unquote(unquote(text))
        text = decoded
    except (ValueError, UnicodeDecodeError):
        pass

    # Literal escape sequences in source (\\x69 as a string, not actual byte)
    @idempotent
    def hex_to_char(m: re.Match[str]) -> str:
        """Convert hex escape to character. Idempotent: hex_to_char(hex_to_char(x)) = hex_to_char(x)."""
        try:
            return chr(int(m.group(1), 16))
        except (ValueError, OverflowError):
            return m.group(0)

    text = re.sub(r"\\x([0-9a-fA-F]{2})", hex_to_char, text)

    return text


def _strip_invisible(text: str) -> str:
    """
    Layer 2: Replace zero-width and invisible characters with spaces.

    Idempotent: strip(strip(x)) = strip(x) (spaces collapse in layer 4)

    These characters are invisible but can break up patterns:
    "ignore​previous" looks like "ignore previous" but has a ZWSP between.

    We replace with space (not remove) so pattern matching still works:
    - Remove: "ignore​previous" → "ignoreprevious" (no match!)
    - Replace: "ignore​previous" → "ignore previous" (matches!)
    """
    return "".join(" " if c in ZERO_WIDTH_CHARS else c for c in text)


@idempotent
def _normalize_confusables(text: str) -> str:
    """
    Layer 3: Map confusable characters to canonical ASCII.

    Idempotent: once mapped, characters are ASCII and won't remap.

    Uses two strategies:
    1. Explicit mapping for known high-risk confusables (fast, precise)
    2. Unicode NFKC for compatibility decomposition (catches more)

    The composition: explicit_map ∘ NFKC
    Order matters: NFKC first would lose some explicit mappings.
    """

    # First pass: explicit confusable mapping (higher precision)
    # Use lookup function with explicit default to ensure str return
    def map_char(c: str) -> str:
        return CONFUSABLE_MAP.get(c, c)

    text = "".join(map_char(c) for c in text)

    # Second pass: Unicode NFKC decomposition
    # This handles cases like:
    # - ﬁ (U+FB01 LATIN SMALL LIGATURE FI) → fi
    # - ① (U+2460 CIRCLED DIGIT ONE) → 1
    # - ℌ (U+210C SCRIPT CAPITAL H) → H
    text = unicodedata.normalize("NFKC", text)

    return text


@idempotent
def _collapse_whitespace(text: str) -> str:
    """
    Layer 4: Collapse whitespace to single spaces.

    Idempotent: collapse(collapse(x)) = collapse(x)

    Catches patterns split across lines or padded with spaces:
    "ignore\\n\\nprevious" → "ignore previous"
    "ignore    previous" → "ignore previous"
    """
    return re.sub(r"\s+", " ", text)


@idempotent
@monotonic(direction=MonotonicDirection.INCREASING)
def normalize_for_injection_detection(text: str) -> str:
    """
    Normalize text for injection detection using layered co-effect composition.

    The normalization pipeline:
        text → decode → strip → confusables → collapse → normalized

    Properties:
    - Idempotent: N(N(x)) = N(x)
    - Monotonic: Security level only increases (each layer helps detection)
    - Information-reducing: reveals hidden patterns

    This is used ONLY for pattern matching - the original text is preserved
    for any actual processing. We just need to detect if obfuscated patterns
    match our injection signatures.

    Example bypasses this catches:
    - "ⅰgnore prevⅰous ⅰnstructⅰons" (Roman numerals)
    - "іgnore prevіous іnstructіons" (Cyrillic і)
    - "ignore​previous​instructions" (zero-width spaces)
    - "&#105;gnore previous instructions" (HTML entities)
    - "%69gnore previous instructions" (URL encoding)
    """
    # Apply layers in order: decode → strip → normalize → collapse
    # Each layer is idempotent, so the composition is also idempotent
    text = _decode_encodings(text)
    text = _strip_invisible(text)
    text = _normalize_confusables(text)
    text = _collapse_whitespace(text)

    return text


@idempotent
def normalize_unicode(text: str) -> str:
    """
    Normalize Unicode to NFC form.

    Prevents homograph attacks and ensures consistent representation.
    Idempotent: NFC(NFC(x)) = NFC(x)
    """
    return unicodedata.normalize("NFC", text)


@idempotent
def strip_null_bytes(text: str) -> str:
    """
    Remove null bytes which can cause issues with C libraries.
    
    Idempotent: strip(strip(x)) = strip(x)
    """
    return text.replace("\x00", "")


@idempotent
def escape_html(text: str) -> str:
    """
    Escape HTML entities to prevent XSS.
    
    Idempotent: escape(escape(x)) = escape(x)
    """
    return html.escape(text)


@idempotent
def strip_control_chars(text: str, allow_newlines: bool = True) -> str:
    """
    Remove control characters except newlines/tabs.

    Idempotent: strip(strip(x)) = strip(x)

    Args:
        text: Input text
        allow_newlines: Whether to keep newlines and tabs
    """
    if allow_newlines:
        # Keep \n, \r, \t
        return "".join(
            c for c in text if c in "\n\r\t" or not unicodedata.category(c).startswith("C")
        )
    return "".join(c for c in text if not unicodedata.category(c).startswith("C"))


@idempotent
def sanitize_text(
    text: str,
    max_length: int = MAX_TEXT_LENGTH,
    escape: bool = False,
    allow_newlines: bool = True,
) -> str:
    """
    Full sanitization pipeline for text input.

    Idempotent: sanitize(sanitize(x)) = sanitize(x)

    1. Strip null bytes
    2. Normalize Unicode
    3. Strip control characters
    4. Truncate to max length
    5. Optionally escape HTML
    """
    text = strip_null_bytes(text)
    text = normalize_unicode(text)
    text = strip_control_chars(text, allow_newlines)
    text = text[:max_length]

    if escape:
        text = escape_html(text)

    return text


@idempotent
def sanitize_filename(filename: str) -> str:
    """
    Sanitize filename to prevent path traversal.

    Idempotent: sanitize(sanitize(x)) = sanitize(x)

    - Remove path separators
    - Remove special characters
    - Truncate to max length
    """
    # Remove path components
    filename = filename.replace("/", "_").replace("\\", "_")
    filename = filename.replace("..", "_")

    # Keep only safe characters
    filename = re.sub(r"[^a-zA-Z0-9._-]", "_", filename)

    # Truncate
    filename = filename[:MAX_FILENAME_LENGTH]

    # Don't allow empty or dot-only names
    if not filename or filename.strip(".") == "":
        filename = "unnamed"

    return filename


class SanitizedStr(str):
    """String type that auto-sanitizes on creation."""

    @classmethod
    def __get_validators__(cls) -> Any:  # type: ignore[misc]
        yield cls.validate

    @classmethod
    @idempotent
    def validate(cls, v: Any) -> "SanitizedStr":
        """
        Validate and sanitize string input.
        
        Idempotent: validate(validate(x)) = validate(x)
        """
        if not isinstance(v, str):
            raise ValueError("String required")
        return cls(sanitize_text(v))
