"""
Voice Engine Protocols - Database, TTS, and STT provider interfaces.

This module defines the protocol interfaces that providers must implement.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal, Protocol


if TYPE_CHECKING:
    from .types import DatabaseRow, DBParams, STTTranscriptionResult


# =============================================================================
# Database Protocol
# =============================================================================


class VoiceDatabaseProtocol(Protocol):
    """Protocol for database interface used by VoiceEngine.

    Compatible with:
    - DatabaseConnection from toolbox.core.db
    - AsyncMock (testing)
    - Any async database with sequence-style params
    """

    async def execute(self, query: str, params: DBParams = ()) -> None:
        """Execute a query with no return value."""
        ...

    async def fetch_one(self, query: str, params: DBParams = ()) -> DatabaseRow | None:
        """Fetch a single row, or None if not found."""
        ...

    async def fetch_all(self, query: str, params: DBParams = ()) -> list[DatabaseRow]:
        """Fetch all matching rows."""
        ...


# =============================================================================
# TTS Provider Protocol
# =============================================================================


class TTSProviderProtocol(Protocol):
    """Protocol for Text-to-Speech providers.

    Implementations:
    - OpenAITTSProvider (OpenAI TTS)
    - ElevenLabsTTSProvider (ElevenLabs)
    - LocalModelTTSProvider (local HuggingFace models)
    - MockTTSProvider (testing)

    Note: get_available_voices is sync because most providers cache the list.
    ElevenLabsTTSProvider fetches async but caches, so it's effectively sync after first call.
    """

    async def synthesize(
        self,
        text: str,
        voice: str,
        model: str | None = None,
        speed: float = 1.0,
        format: str = "mp3",
    ) -> bytes:
        """
        Synthesize speech from text.

        Args:
            text: Text to synthesize (1-4096 chars)
            voice: Voice ID or name
            model: Model ID (provider-specific)
            speed: Speed multiplier (0.25-4.0)
            format: Audio format (mp3, wav, etc.)

        Returns:
            Raw audio bytes

        Raises:
            ValueError: If parameters are invalid
            RuntimeError: If synthesis fails
        """
        ...

    def get_available_voices(self) -> list[str]:
        """Get list of available voice IDs.

        Implementations should cache voices to make this effectively sync.
        """
        ...

    def estimate_cost(self, text: str, model: str | None = None) -> float:
        """Estimate cost in USD for synthesizing text."""
        ...


# =============================================================================
# STT Provider Protocol
# =============================================================================


class STTProviderProtocol(Protocol):
    """Protocol for Speech-to-Text providers.

    Implementations:
    - OpenAIWhisperProvider (OpenAI Whisper)
    - DeepgramSTTProvider (Deepgram)
    - MockSTTProvider (testing)
    """

    async def transcribe(
        self,
        audio_data: bytes,
        audio_format: Literal["mp3", "wav", "ogg", "flac", "webm", "m4a"],
        language: str = "en",
        include_timestamps: bool = False,
    ) -> STTTranscriptionResult:
        """
        Transcribe audio to text.

        Args:
            audio_data: Raw audio bytes (max 25MB)
            audio_format: Audio format
            language: ISO 639-1 language code
            include_timestamps: Include word-level timestamps

        Returns:
            Transcription result with text and metadata

        Raises:
            ValueError: If parameters are invalid
            RuntimeError: If transcription fails
        """
        ...

    def estimate_cost(self, audio_duration_seconds: float) -> float:
        """Estimate cost in USD for transcribing audio."""
        ...


# =============================================================================
# Exports
# =============================================================================

__all__ = [
    "VoiceDatabaseProtocol",
    "TTSProviderProtocol",
    "STTProviderProtocol",
]
