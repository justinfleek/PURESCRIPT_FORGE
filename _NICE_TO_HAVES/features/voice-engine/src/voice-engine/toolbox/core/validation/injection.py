"""
Prompt Injection Detection

Detects potential prompt injection attempts in user input.
Uses layered normalization to catch obfuscation bypasses.
"""

from enum import Enum
from typing import Any, cast

from toolbox.core.effects import idempotent, monotonic, MonotonicDirection

from .constants import INJECTION_REGEX
from .sanitizers import normalize_for_injection_detection


class InjectionRisk(Enum):
    """Risk level for potential injection."""

    NONE = "none"
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"


@idempotent
@monotonic(direction=MonotonicDirection.INCREASING)
def detect_injection(text: str) -> tuple[InjectionRisk, list[str]]:
    """
    Detect potential prompt injection attempts.

    Idempotent: detect(detect(x)) = detect(x)
    Monotonic: Security level only increases (never decreases)

    Uses layered normalization to catch obfuscation bypasses:
    - Unicode confusables (ⅰ → i, Cyrillic і → i)
    - Zero-width characters (invisible separators)
    - HTML entities (&#105; → i)
    - URL encoding (%69 → i)
    - Hex escapes (\\x69 → i)

    Returns:
        Tuple of (risk_level, list of matched patterns)
    """
    # Normalize text to catch obfuscation attempts
    # This is safe because we only use the normalized form for pattern matching
    # The original text is preserved for actual processing
    normalized = normalize_for_injection_detection(text)

    # Check both original and normalized (defense in depth)
    # Some patterns might be in the original that normalization changes
    all_matches: list[str] = []

    for check_text in [text, normalized]:
        matches = INJECTION_REGEX.findall(check_text)
        if matches:
            # Flatten matches (regex may return tuples for groups)
            for m in matches:
                if isinstance(m, tuple):
                    tuple_m = cast("tuple[Any, ...]", m)
                    all_matches.extend(str(s) for s in tuple_m if s)
                else:
                    all_matches.append(str(m) if m else "")

    if not all_matches:
        return InjectionRisk.NONE, []

    # Deduplicate and lowercase
    unique_matches: list[str] = list(set(s.lower() for s in all_matches if s))

    if len(unique_matches) >= 3:
        return InjectionRisk.HIGH, unique_matches
    if len(unique_matches) >= 2:
        return InjectionRisk.MEDIUM, unique_matches
    return InjectionRisk.LOW, unique_matches


@idempotent
@monotonic(direction=MonotonicDirection.INCREASING)
def contains_injection(text: str, min_risk: InjectionRisk = InjectionRisk.LOW) -> bool:
    """
    Check if text contains injection patterns at or above given risk level.

    Idempotent: contains(contains(x)) = contains(x)
    Monotonic: Security level only increases
    """
    risk, _ = detect_injection(text)
    risk_levels = [InjectionRisk.NONE, InjectionRisk.LOW, InjectionRisk.MEDIUM, InjectionRisk.HIGH]
    return risk_levels.index(risk) >= risk_levels.index(min_risk)
