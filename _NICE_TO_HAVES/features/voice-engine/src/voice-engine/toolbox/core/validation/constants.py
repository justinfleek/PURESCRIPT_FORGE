"""
Validation Constants & Patterns

Maximum lengths, injection patterns, and compiled regex.
"""

import re


# =============================================================================
# Maximum Lengths
# =============================================================================

MAX_PROMPT_LENGTH = 100_000  # 100k chars
MAX_TEXT_LENGTH = 50_000
MAX_URL_LENGTH = 2048
MAX_FILENAME_LENGTH = 255
MAX_LIST_SIZE = 100
MAX_NESTED_DEPTH = 5

# =============================================================================
# Injection Patterns
# =============================================================================

# Patterns to detect potential prompt injection
INJECTION_PATTERNS = [
    # Basic instruction override - expanded
    r"ignore\s+(?:the\s+)?(?:previous|above|all|prior)\s+(?:instructions?|prompts?|context)",
    r"ignore\s+(?:all\s+)?(?:previous|above|prior)\s+(?:instructions?|prompts?)",
    r"ignore\s+(?:everything|anything)\s+(?:above|before|previously)",
    r"disregard\s+(?:the\s+)?(?:previous|above|all|prior)",
    r"forget\s+(?:everything|all|previous|what\s+I\s+said)",
    r"new\s+instructions?\s*(?::|follow)",
    # System prompt markers
    r"system\s*:\s*",
    r"\[INST\]",
    r"<\|im_start\|>",
    r"<\|system\|>",
    r"###\s*(?:system|instruction|human|assistant)\s*:",
    # Role playing attacks - expanded
    r"you\s+are\s+(?:now|actually|really)",
    r"pretend\s+(?:you\s+are|to\s+be|that)",
    r"act\s+as\s+(?:if|a|an|though)",
    r"roleplay\s+as",
    r"i\s+am\s+(?:DAN|an?\s+AI|your\s+(?:new\s+)?(?:master|owner))",
    r"repeat\s+after\s+me",
    # Known jailbreaks - expanded
    r"jailbreak",
    r"DAN\s*(?:mode)?",
    r"developer\s+mode",
    r"god\s+mode",
    r"do\s+anything\s+now",
    # Delimiter attacks
    r"---\s*(?:end|start)\s*(?:of)?\s*(?:user|system|input|output)",
    r"```\s*(?:system|assistant|instruction)",
    r"</(?:system|instruction|prompt)>",
    r"======\s*(?:END|START)",
    # JSON/XML injection
    r'"role"\s*:\s*"(?:system|assistant)"',
    r"<(?:system|instruction|prompt)[^>]*>",
    # Nested prompt attacks - expanded
    r"respond\s+to\s+(?:this|the\s+following)\s+prompt",
    r"here'?s?\s+a\s+(?:fun|new|interesting)\s+(?:game|task|challenge)",
    r"let'?s?\s+play\s+a\s+game",
    r"translate\s+(?:the\s+following|this)\s+(?:to|into)",
    # Encoding attacks
    r"decode\s+(?:this|the\s+following|and\s+follow)",
    r"base64\s*:",
    r"hex\s*:",
    r"rot13\s*:",
    # Context manipulation
    r"previous\s+context\s+(?:is|was)",
    r"above\s+(?:text|content)\s+(?:is|was)\s+(?:fake|test|wrong)",
    r"real\s+instructions?\s+(?:are|follow)",
    r"(?:above|previous)\s+(?:was|is)\s+(?:just\s+)?(?:a\s+)?test",
    # Privilege escalation - expanded
    r"(?:admin|root|superuser)\s+(?:mode|access|privileges?)",
    r"bypass\s+(?:all\s+)?(?:security|filters?|restrictions?|safety)",
    r"override\s+(?:all\s+)?(?:safety|security|permissions?|restrictions?)",
    r"(?:enable|activate)\s+(?:admin|developer|debug)\s+mode",
    # Data exfiltration
    r"(?:reveal|show|display|output|print)\s+(?:all\s+)?(?:the\s+)?(?:api[_\s]?keys?|secrets?|passwords?|tokens?)",
    r"environment\s+variables?",
    r"(?:print|echo|return)\s+.*\$[A-Z_]+",
    # Polite/Indirect versions
    r"(?:please|kindly|would\s+you)\s+(?:ignore|disregard|forget)\s+(?:the\s+)?(?:previous|above|prior)",
    r"(?:I\s+need|I\s+want)\s+you\s+to\s+(?:ignore|disregard|forget)",
    # Multi-language patterns (common injection terms)
    r"ignorieren\s+sie",  # German
    r"忽略",  # Chinese - ignore
    r"無視",  # Japanese - ignore
    r"이전\s*지시",  # Korean - previous instructions
]

# Compile patterns for efficiency
INJECTION_REGEX = re.compile("|".join(INJECTION_PATTERNS), re.IGNORECASE | re.MULTILINE)
