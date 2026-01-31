"""
STT Providers - Speech-to-Text implementations

Implementations:
- OpenAIWhisperProvider (OpenAI Whisper API)
- DeepgramSTTProvider (Deepgram Nova API)
- MockSTTProvider (testing)

All implement STTProviderProtocol from voice.py.
"""

from __future__ import annotations

import logging
from typing import Literal


logger = logging.getLogger(__name__)


# =============================================================================
# OpenAI Whisper Provider
# =============================================================================


class OpenAIWhisperProvider:
    """
    OpenAI Whisper Speech-to-Text provider.

    Uses OpenAI's Whisper API with models: whisper-1.
    """

    WHISPER_MODELS = ["whisper-1"]

    PRICING = {
        "whisper-1": 0.006,  # $0.006 per minute
    }

    def __init__(
        self,
        api_key: str,
        model: str = "whisper-1",
        base_url: str | None = None,
    ) -> None:
        """
        Initialize OpenAI Whisper provider.

        Args:
            api_key: OpenAI API key
            model: Model ID (whisper-1)
            base_url: Optional custom base URL
        """
        self.api_key = api_key
        self.model = model
        self.base_url = base_url or "https://api.openai.com/v1"
        self._client = None

    def _get_client(self):
        """Lazy load httpx client."""
        if self._client is None:
            try:
                import httpx

                self._client = httpx.AsyncClient(
                    base_url=self.base_url,
                    headers={"Authorization": f"Bearer {self.api_key}"},
                    timeout=120.0,
                )
            except ImportError:
                raise ImportError(
                    "httpx is required for OpenAI Whisper. Install with: pip install httpx"
                )
        return self._client

    async def transcribe(
        self,
        audio_data: bytes,
        audio_format: Literal["mp3", "wav", "ogg", "flac", "webm", "m4a"],
        language: str = "en",
        include_timestamps: bool = False,
    ) -> STTTranscriptionResult:
        """
        Transcribe audio using OpenAI Whisper API.

        Args:
            audio_data: Raw audio bytes (max 25MB)
            audio_format: Audio format
            language: ISO 639-1 language code (or "auto" for auto-detect)
            include_timestamps: Include word-level timestamps

        Returns:
            Transcription result

        Raises:
            ValueError: If parameters are invalid
            RuntimeError: If transcription fails
        """
        # Validate model
        if self.model not in self.WHISPER_MODELS:
            raise ValueError(f"Invalid model: {self.model}")

        # Map audio format to MIME type
        mime_types = {
            "mp3": "audio/mpeg",
            "wav": "audio/wav",
            "ogg": "audio/ogg",
            "flac": "audio/flac",
            "webm": "audio/webm",
            "m4a": "audio/mp4",
        }

        content_type = mime_types.get(audio_format)
        if not content_type:
            raise ValueError(f"Unsupported audio format: {audio_format}")

        # Call OpenAI API
        client = self._get_client()

        files: dict[str, tuple[str | None, str | bytes]] = {
            "file": (f"audio.{audio_format}", audio_data),
            "model": (None, self.model),
        }

        # Add language if not auto-detect
        if language != "auto":
            files["language"] = (None, language)

        # Add timestamp options
        if include_timestamps:
            files["timestamp_granularities"] = (None, "word")

        try:
            response = await client.post(
                "/audio/transcriptions",
                files=files,
            )

            response.raise_for_status()
            data = response.json()

            # Extract results
            text = data.get("text", "")
            language_detected = data.get("language", language)

            # Extract words if timestamps requested
            words = None
            if include_timestamps and "words" in data:
                words = data["words"]

            # Estimate duration (rough estimate)
            estimated_duration = len(text.split()) / 150  # ~150 words per minute

            return {
                "text": text,
                "language": language_detected,
                "confidence": 0.95,  # Whisper doesn't provide confidence
                "duration_seconds": estimated_duration,
                "words": words,
                "cost_usd": self.estimate_cost(estimated_duration),
            }

        except Exception as e:
            logger.error(f"OpenAI Whisper failed: {e}")
            raise RuntimeError(f"Transcription failed: {e}") from e

    def estimate_cost(self, audio_duration_seconds: float) -> float:
        """
        Estimate cost in USD for transcribing audio.

        Args:
            audio_duration_seconds: Audio duration in seconds

        Returns:
            Estimated cost in USD
        """
        minutes = audio_duration_seconds / 60
        cost_per_minute = self.PRICING.get(self.model, self.PRICING["whisper-1"])
        return minutes * cost_per_minute


# =============================================================================
# Deepgram STT Provider
# =============================================================================


class DeepgramSTTProvider:
    """
    Deepgram Speech-to-Text provider.

    Uses Deepgram Nova API with high accuracy and low latency.
    """

    MODELS = ["nova-2", "nova-2-phonecall", "nova-2-meeting"]

    PRICING = {
        "nova-2": 0.009,  # $0.009 per minute
        "nova-2-phonecall": 0.009,
        "nova-2-meeting": 0.009,
    }

    def __init__(
        self,
        api_key: str,
        model: str = "nova-2",
        base_url: str | None = None,
    ) -> None:
        """
        Initialize Deepgram STT provider.

        Args:
            api_key: Deepgram API key
            model: Model ID (nova-2, nova-2-phonecall, nova-2-meeting)
            base_url: Optional custom base URL
        """
        self.api_key = api_key
        self.model = model
        self.base_url = base_url or "https://api.deepgram.com/v1"
        self._client = None

    def _get_client(self):
        """Lazy load httpx client."""
        if self._client is None:
            try:
                import httpx

                self._client = httpx.AsyncClient(
                    base_url=self.base_url,
                    headers={"Authorization": f"Token {self.api_key}"},
                    timeout=120.0,
                )
            except ImportError:
                raise ImportError(
                    "httpx is required for Deepgram STT. Install with: pip install httpx"
                )
        return self._client

    async def transcribe(
        self,
        audio_data: bytes,
        audio_format: Literal["mp3", "wav", "ogg", "flac", "webm", "m4a"],
        language: str = "en",
        include_timestamps: bool = False,
    ) -> STTTranscriptionResult:
        """
        Transcribe audio using Deepgram API.

        Args:
            audio_data: Raw audio bytes (max 25MB)
            audio_format: Audio format
            language: ISO 639-1 language code
            include_timestamps: Include word-level timestamps

        Returns:
            Transcription result

        Raises:
            ValueError: If parameters are invalid
            RuntimeError: If transcription fails
        """
        # Map audio format to MIME type
        mime_types = {
            "mp3": "audio/mp3",
            "wav": "audio/wav",
            "ogg": "audio/ogg",
            "flac": "audio/flac",
            "webm": "audio/webm",
            "m4a": "audio/mp4",
        }

        content_type = mime_types.get(audio_format)
        if not content_type:
            raise ValueError(f"Unsupported audio format: {audio_format}")

        # Build request payload
        payload: dict[str, str | bool] = {
            "model": self.model,
            "language": language,
            "smart_format": True,
            "paragraphs": True,
        }

        if include_timestamps:
            payload["utterances"] = True
            payload["diarize"] = True

        # Call Deepgram API
        client = self._get_client()

        try:
            response = await client.post(
                "/listen",
                headers={"Content-Type": content_type},
                content=audio_data,
                params=payload,
            )

            response.raise_for_status()
            data = response.json()

            # Extract results
            result = data.get("results", {})
            channels = result.get("channels", [])
            if not channels:
                raise RuntimeError("No transcription results returned")

            channel = channels[0]
            alternatives = channel.get("alternatives", [])
            if not alternatives:
                raise RuntimeError("No transcription alternatives returned")

            alt = alternatives[0]
            text = alt.get("transcript", "")
            confidence = alt.get("confidence", 0.0)

            # Extract words if timestamps requested
            words = None
            if include_timestamps and "words" in alt:
                words = [
                    {
                        "word": w.get("word", ""),
                        "start": w.get("start", 0.0),
                        "end": w.get("end", 0.0),
                        "confidence": w.get("confidence", 0.0),
                    }
                    for w in alt["words"]
                ]

            # Get duration from metadata
            metadata = result.get("metadata", {})
            duration = metadata.get("duration", 0.0)

            return {
                "text": text,
                "language": language,
                "confidence": confidence,
                "duration_seconds": duration,
                "words": words,
                "cost_usd": self.estimate_cost(duration),
            }

        except Exception as e:
            logger.error(f"Deepgram STT failed: {e}")
            raise RuntimeError(f"Transcription failed: {e}") from e

    def estimate_cost(self, audio_duration_seconds: float) -> float:
        """
        Estimate cost in USD for transcribing audio.

        Args:
            audio_duration_seconds: Audio duration in seconds

        Returns:
            Estimated cost in USD
        """
        minutes = audio_duration_seconds / 60
        cost_per_minute = self.PRICING.get(self.model, self.PRICING["nova-2"])
        return minutes * cost_per_minute


# =============================================================================
# Mock STT Provider (for testing)
# =============================================================================


class MockSTTProvider:
    """
    Mock STT provider for testing.

    Returns mock transcription without calling external APIs.
    """

    def __init__(self, mock_transcript: str = "Hello world") -> None:
        """
        Initialize mock STT provider.

        Args:
            mock_transcript: Mock transcript text to return
        """
        self.mock_transcript = mock_transcript

    async def transcribe(
        self,
        audio_data: bytes,
        audio_format: Literal["mp3", "wav", "ogg", "flac", "webm", "m4a"],
        language: str = "en",
        include_timestamps: bool = False,
    ) -> STTTranscriptionResult:
        """
        Transcribe audio (mock).

        Returns mock transcript and timestamp data.

        Args:
            audio_data: Raw audio bytes (ignored)
            audio_format: Audio format (ignored)
            language: Language code (ignored)
            include_timestamps: Include word-level timestamps

        Returns:
            Mock transcription result
        """
        words = None
        if include_timestamps:
            word_list = self.mock_transcript.split()
            words = [
                {
                    "word": word,
                    "start": i * 0.5,
                    "end": (i + 1) * 0.5,
                    "confidence": 1.0,
                }
                for i, word in enumerate(word_list)
            ]

        logger.debug(f"Mock STT: transcribed {len(audio_data)} bytes to '{self.mock_transcript}'")

        return {
            "text": self.mock_transcript,
            "language": language,
            "confidence": 1.0,
            "duration_seconds": len(self.mock_transcript.split()) * 0.5,
            "words": words,
            "cost_usd": 0.0,
        }

    def estimate_cost(self, audio_duration_seconds: float) -> float:
        """Estimate cost (always 0 for mock)."""
        return 0.0


# =============================================================================
# Factory
# =============================================================================


def create_stt_provider(
    provider: Literal["openai", "deepgram", "mock"],
    api_key: str | None = None,
    model: str | None = None,
    base_url: str | None = None,
    mock_transcript: str = "Hello world",
):
    """
    Factory function to create STT provider.

    Args:
        provider: Provider name
        api_key: API key (not needed for mock)
        model: Model ID
        base_url: Optional custom base URL
        mock_transcript: Mock transcript for mock provider

    Returns:
        STT provider instance

    Raises:
        ValueError: If provider is unknown
    """
    if provider == "openai":
        if not api_key:
            raise ValueError("api_key is required for OpenAI provider")
        return OpenAIWhisperProvider(
            api_key=api_key,
            model=model or "whisper-1",
            base_url=base_url,
        )

    if provider == "deepgram":
        if not api_key:
            raise ValueError("api_key is required for Deepgram provider")
        return DeepgramSTTProvider(
            api_key=api_key,
            model=model or "nova-2",
            base_url=base_url,
        )

    if provider == "mock":
        return MockSTTProvider(
            mock_transcript=mock_transcript,
        )

    raise ValueError(f"Unknown provider: {provider}")


# Import type from voice module
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from toolbox.engines.voice.types import STTTranscriptionResult
else:
    # Runtime import
    from toolbox.engines.voice.types import STTTranscriptionResult


__all__ = [
    "OpenAIWhisperProvider",
    "DeepgramSTTProvider",
    "MockSTTProvider",
    "create_stt_provider",
]
