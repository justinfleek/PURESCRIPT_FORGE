"""
Voice Engine Types - Database primitives, enums, and TypedDicts.

This module contains all type definitions used by the voice engine.
"""

from __future__ import annotations

from enum import Enum
from typing import Literal

from typing_extensions import TypedDict

# =============================================================================
# Database Primitive Types - Import from canonical location
# =============================================================================

from toolbox.core.db.types import DBParams, DBPrimitive, DatabaseRow

__all__ = [
    "DBPrimitive",
    "DatabaseRow",
    "DBParams",
]


def _str_from_db(value: DBPrimitive, default: str = "") -> str:
    """Extract string from DBPrimitive with type safety."""
    if isinstance(value, str):
        return value
    return str(value) if value else default


def _str_or_empty_from_db(value: DBPrimitive) -> str:
    """Extract string from DBPrimitive, returning empty string for non-string values."""
    if isinstance(value, str):
        return value
    return str(value) if value else ""


def _float_from_db(value: DBPrimitive, default: float = 0.0) -> float:
    """Extract float from DBPrimitive with type safety."""
    if isinstance(value, float):
        return value
    if isinstance(value, int):
        return float(value)
    return default


def _float_or_zero_from_db(value: DBPrimitive) -> float:
    """Extract float from DBPrimitive, returning 0.0 for invalid values."""
    if isinstance(value, float):
        return value
    if isinstance(value, int):
        return float(value)
    return 0.0


def _int_from_db(value: DBPrimitive, default: int = 0) -> int:
    """Extract int from DBPrimitive with type safety."""
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    if isinstance(value, float):
        return int(value)
    return default


def _str_or_none_from_db(value: DBPrimitive | None) -> str | None:
    """Extract string from DBPrimitive, returning None for None/empty values."""
    if value is None:
        return None
    if isinstance(value, str):
        return value if value else None
    return str(value) if value else None


def _float_or_none_from_db(value: DBPrimitive | None) -> float | None:
    """Extract float from DBPrimitive, returning None for None/invalid values."""
    if value is None:
        return None
    if isinstance(value, float):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return float(value)
    return None


# =============================================================================
# Enums
# =============================================================================


class VoiceChatMode(str, Enum):
    """Voice chat interaction modes."""

    PUSH_TO_TALK = "push_to_talk"
    VOICE_ACTIVITY = "voice_activity"
    CONTINUOUS = "continuous"
    WAKE_WORD = "wake_word"


class VoiceChatState(str, Enum):
    """Voice chat session states."""

    IDLE = "idle"
    LISTENING = "listening"
    PROCESSING = "processing"
    THINKING = "thinking"
    SPEAKING = "speaking"
    INTERRUPTED = "interrupted"
    ERROR = "error"
    ENDED = "ended"


class VoiceQuality(str, Enum):
    """Voice output quality levels."""

    STANDARD = "standard"
    HD = "hd"
    REALTIME = "realtime"


class AudioFormat(str, Enum):
    """Audio file formats."""

    MP3 = "mp3"
    WAV = "wav"
    OGG = "ogg"
    FLAC = "flac"
    WEBM = "webm"
    PCM = "pcm"
    OPUS = "opus"


# =============================================================================
# TypedDicts
# =============================================================================


class STTTranscriptionResult(TypedDict):
    """Result of speech-to-text transcription."""

    text: str
    language: str
    confidence: float
    duration_seconds: float
    words: list[dict[str, float | str]]
    cost_usd: float


class TTSRequest(TypedDict, total=False):
    """Text-to-speech request."""

    text: str
    voice: str
    model: str
    quality: VoiceQuality
    format: AudioFormat
    speed: float
    language: str


class TTSResponse(TypedDict):
    """Text-to-speech response."""

    audio_data: bytes
    audio_format: AudioFormat
    duration_seconds: float
    characters_used: int
    cost_usd: float
    voice: str


class VoiceChatMessage(TypedDict):
    """Voice chat message."""

    id: str
    conversation_id: str
    role: Literal["user", "assistant"]
    text: str
    audio_url: str
    duration_seconds: float
    stt_confidence: float
    created_at: str


class VoiceChatConfig(TypedDict, total=False):
    """Voice chat session configuration."""

    voice: str
    quality: VoiceQuality
    mode: VoiceChatMode
    language: str
    speed: float
    vad_threshold: float
    silence_timeout_ms: int
    max_duration_seconds: int
    interrupt_enabled: bool


class VoiceChatSession(TypedDict):
    """Voice chat session."""

    id: str
    conversation_id: str
    org_id: str
    user_id: str
    config: VoiceChatConfig
    state: VoiceChatState
    messages: list[VoiceChatMessage]
    total_audio_seconds: float
    total_stt_tokens: int
    total_tts_characters: int
    started_at: str
    ended_at: str


# =============================================================================
# Exports
# =============================================================================

__all__ = [
    # Database primitives
    "DBPrimitive",
    "DatabaseRow",
    "_str_from_db",
    "_str_or_empty_from_db",
    "_str_or_none_from_db",
    "_float_from_db",
    "_float_or_zero_from_db",
    "_float_or_none_from_db",
    "_int_from_db",
    # Enums
    "VoiceChatMode",
    "VoiceChatState",
    "VoiceQuality",
    "AudioFormat",
    # TypedDicts
    "STTTranscriptionResult",
    "TTSRequest",
    "TTSResponse",
    "VoiceChatMessage",
    "VoiceChatConfig",
    "VoiceChatSession",
]
