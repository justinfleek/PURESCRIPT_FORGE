"""
TTS Providers - Text-to-Speech implementations

Implementations:
- OpenAITTSProvider (OpenAI TTS API)
- ElevenLabsTTSProvider (ElevenLabs API)
- MockTTSProvider (testing)

All implement TTSProviderProtocol from voice.py.
"""

from __future__ import annotations

import logging
from typing import TYPE_CHECKING, Literal


if TYPE_CHECKING:
    from toolbox.engines.voice_local_provider import VoiceDatabaseProtocol

logger = logging.getLogger(__name__)


# =============================================================================
# OpenAI TTS Provider
# =============================================================================


class OpenAITTSProvider:
    """
    OpenAI Text-to-Speech provider.

    Uses OpenAI's TTS API with voices: alloy, echo, fable, onyx, nova, shimmer.
    """

    OPENAI_VOICES = ["alloy", "echo", "fable", "onyx", "nova", "shimmer"]

    OPENAI_MODELS = {
        "tts-1": 0.015,  # $0.015 per 1K characters
        "tts-1-hd": 0.030,  # $0.030 per 1K characters
    }

    def __init__(
        self,
        api_key: str,
        model: str = "tts-1",
        default_voice: str = "alloy",
        base_url: str | None = None,
    ) -> None:
        """
        Initialize OpenAI TTS provider.

        Args:
            api_key: OpenAI API key
            model: Model ID (tts-1 or tts-1-hd)
            default_voice: Default voice ID
            base_url: Optional custom base URL
        """
        self.api_key = api_key
        self.model = model
        self.default_voice = default_voice
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
                    timeout=60.0,
                )
            except ImportError:
                raise ImportError(
                    "httpx is required for OpenAI TTS. Install with: pip install httpx"
                )
        return self._client

    async def synthesize(
        self,
        text: str,
        voice: str,
        model: str | None = None,
        speed: float = 1.0,
        format: str = "mp3",
    ) -> bytes:
        """
        Synthesize speech using OpenAI TTS API.

        Args:
            text: Text to synthesize
            voice: Voice ID (alloy, echo, fable, onyx, nova, shimmer)
            model: Model ID (overrides default)
            speed: Speed multiplier (0.25-4.0)
            format: Audio format (mp3, opus, aac, flac, wav, pcm)

        Returns:
            Raw audio bytes

        Raises:
            ValueError: If parameters are invalid
            RuntimeError: If synthesis fails
        """
        voice = voice or self.default_voice

        # Validate voice
        if voice not in self.OPENAI_VOICES:
            raise ValueError(f"Invalid voice: {voice}. Valid voices: {self.OPENAI_VOICES}")

        # Validate model
        model = model or self.model
        if model not in self.OPENAI_MODELS:
            raise ValueError(
                f"Invalid model: {model}. Valid models: {list(self.OPENAI_MODELS.keys())}"
            )

        # Validate format
        valid_formats = ["mp3", "opus", "aac", "flac", "wav", "pcm"]
        if format not in valid_formats:
            raise ValueError(f"Invalid format: {format}. Valid formats: {valid_formats}")

        # Call OpenAI API
        client = self._get_client()

        try:
            response = await client.post(
                "/audio/speech",
                json={
                    "model": model,
                    "input": text,
                    "voice": voice,
                    "speed": speed,
                    "response_format": format,
                },
            )

            response.raise_for_status()
            return response.content

        except Exception as e:
            logger.error(f"OpenAI TTS failed: {e}")
            raise RuntimeError(f"TTS synthesis failed: {e}") from e

    def get_available_voices(self) -> list[str]:
        """Get list of available voice IDs."""
        return self.OPENAI_VOICES.copy()

    def estimate_cost(self, text: str, model: str | None = None) -> float:
        """
        Estimate cost in USD for synthesizing text.

        Args:
            text: Text to synthesize
            model: Model ID (uses default if None)

        Returns:
            Estimated cost in USD
        """
        model = model or self.model
        cost_per_1k = self.OPENAI_MODELS.get(model, self.OPENAI_MODELS["tts-1"])
        return (len(text) / 1000) * cost_per_1k


# =============================================================================
# ElevenLabs TTS Provider
# =============================================================================


class ElevenLabsTTSProvider:
    """
    ElevenLabs Text-to-Speech provider.

    Uses ElevenLabs API with ultra-realistic voices.
    """

    def __init__(
        self,
        api_key: str,
        model: str = "eleven_monolingual_v1",
        default_voice: str = "21m00Tcm4TlvDq8ikWAM",
        base_url: str | None = None,
    ) -> None:
        """
        Initialize ElevenLabs TTS provider.

        Args:
            api_key: ElevenLabs API key
            model: Model ID
            default_voice: Default voice ID
            base_url: Optional custom base URL
        """
        self.api_key = api_key
        self.model = model
        self.default_voice = default_voice
        self.base_url = base_url or "https://api.elevenlabs.io/v1"
        self._client = None
        self._voices_cache: list[str] | None = None

    def _get_client(self):
        """Lazy load httpx client."""
        if self._client is None:
            try:
                import httpx

                self._client = httpx.AsyncClient(
                    base_url=self.base_url,
                    headers={"xi-api-key": self.api_key},
                    timeout=60.0,
                )
            except ImportError:
                raise ImportError(
                    "httpx is required for ElevenLabs TTS. Install with: pip install httpx"
                )
        return self._client

    async def synthesize(
        self,
        text: str,
        voice: str,
        model: str | None = None,
        speed: float = 1.0,
        format: str = "mp3",
    ) -> bytes:
        """
        Synthesize speech using ElevenLabs API.

        Args:
            text: Text to synthesize
            voice: Voice ID
            model: Model ID (overrides default)
            speed: Speed multiplier (0.25-4.0)
            format: Audio format (mp3_44100, mp3_22050, pcm, etc.)

        Returns:
            Raw audio bytes

        Raises:
            ValueError: If parameters are invalid
            RuntimeError: If synthesis fails
        """
        voice = voice or self.default_voice
        model = model or self.model

        # Validate speed
        if not (0.25 <= speed <= 4.0):
            raise ValueError(f"Speed must be in [0.25, 4.0], got {speed}")

        # Map format
        format_map = {
            "mp3": "mp3_44100",
            "wav": "pcm_16000",
            "flac": "flac",
        }
        _eleven_format = format_map.get(format, "mp3_44100")  # Reserved for API call

        # Call ElevenLabs API
        client = self._get_client()

        try:
            response = await client.post(
                f"/text-to-speech/{voice}",
                headers={
                    "Content-Type": "application/json",
                    "Accept": "audio/mpeg",
                },
                json={
                    "text": text,
                    "model_id": model,
                    "voice_settings": {
                        "stability": 0.5,
                        "similarity_boost": 0.75,
                    },
                },
            )

            response.raise_for_status()
            return response.content

        except Exception as e:
            logger.error(f"ElevenLabs TTS failed: {e}")
            raise RuntimeError(f"TTS synthesis failed: {e}") from e

    def get_available_voices(self) -> list[str]:
        """
        Get list of available voice IDs.

        Returns cached voices if available, otherwise default voice.
        Call fetch_voices() to populate cache from ElevenLabs API.

        Returns:
            List of voice IDs
        """
        if self._voices_cache is not None:
            return self._voices_cache
        # Return default voice if cache not populated
        # Use fetch_voices() to populate from API
        return [self.default_voice]

    async def fetch_voices(self) -> list[str]:
        """
        Fetch and cache available voice IDs from ElevenLabs API.

        Call this once to populate the voices cache, then use
        get_available_voices() for sync access.

        Returns:
            List of voice IDs
        """
        if self._voices_cache is not None:
            return self._voices_cache

        client = self._get_client()

        try:
            response = await client.get("/voices")
            response.raise_for_status()

            data = response.json()
            voices: list[str] = [v["voice_id"] for v in data.get("voices", [])]
            self._voices_cache = voices

            return voices

        except Exception as e:
            logger.error(f"Failed to fetch voices: {e}")
            return [self.default_voice]

    def estimate_cost(self, text: str, model: str | None = None) -> float:
        """
        Estimate cost in USD for synthesizing text.

        ElevenLabs pricing varies by tier. This is a rough estimate.

        Args:
            text: Text to synthesize
            model: Model ID

        Returns:
            Estimated cost in USD
        """
        # Rough estimate: $0.30 per 1,000 characters for starter tier
        return (len(text) / 1000) * 0.30


# =============================================================================
# Import Local Provider
# =============================================================================

from toolbox.engines.voice_local_provider import (
    LocalModelTTSProvider,
    create_local_model_tts_provider,
)


# =============================================================================
# Mock TTS Provider (for testing)
# =============================================================================


class MockTTSProvider:
    """
    Mock TTS provider for testing.

    Returns mock audio data without calling external APIs.
    """

    MOCK_VOICES = ["mock_voice_1", "mock_voice_2", "mock_voice_3"]

    def __init__(
        self,
        default_voice: str = "mock_voice_1",
    ) -> None:
        """
        Initialize mock TTS provider.

        Args:
            default_voice: Default voice ID
        """
        self.default_voice = default_voice

    async def synthesize(
        self,
        text: str,
        voice: str,
        model: str | None = None,
        speed: float = 1.0,
        format: str = "mp3",
    ) -> bytes:
        """
        Synthesize mock speech.

        Returns a placeholder MP3 header + text as audio.

        Args:
            text: Text to synthesize
            voice: Voice ID
            model: Model ID (ignored)
            speed: Speed multiplier (ignored)
            format: Audio format (ignored)

        Returns:
            Mock audio bytes
        """
        # Mock MP3 header (ID3v2)
        header = b"ID3\x04\x00\x00\x00\x00\x00\x00"
        # Add text as mock audio data
        mock_audio = header + text.encode("utf-8")

        logger.debug(f"Mock TTS: synthesized {len(text)} chars for voice '{voice}'")
        return mock_audio

    def get_available_voices(self) -> list[str]:
        """Get list of mock voice IDs."""
        return self.MOCK_VOICES.copy()

    def estimate_cost(self, text: str, model: str | None = None) -> float:
        """Estimate cost (always 0 for mock)."""
        return 0.0


# =============================================================================
# Factory
# =============================================================================


def create_tts_provider(
    provider: Literal["openai", "elevenlabs", "local", "mock"],
    api_key: str | None = None,
    model: str | None = None,
    default_voice: str | None = None,
    base_url: str | None = None,
    db: VoiceDatabaseProtocol | None = None,
    model_id: str | None = None,
) -> OpenAITTSProvider | ElevenLabsTTSProvider | LocalModelTTSProvider | MockTTSProvider:
    """
    Factory function to create TTS provider.

    Args:
        provider: Provider name (openai, elevenlabs, local, mock)
        api_key: API key (not needed for mock or local)
        model: Model ID (for cloud providers)
        default_voice: Default voice ID
        base_url: Optional custom base URL
        db: Database connection (required for local provider)
        model_id: Model ID from MODELS_REGISTRY (required for local provider)

    Returns:
        TTS provider instance

    Raises:
        ValueError: If provider is unknown or missing required params
    """
    if provider == "openai":
        if not api_key:
            raise ValueError("api_key is required for OpenAI provider")
        return OpenAITTSProvider(
            api_key=api_key,
            model=model or "tts-1",
            default_voice=default_voice or "alloy",
            base_url=base_url,
        )

    if provider == "elevenlabs":
        if not api_key:
            raise ValueError("api_key is required for ElevenLabs provider")
        return ElevenLabsTTSProvider(
            api_key=api_key,
            model=model or "eleven_monolingual_v1",
            default_voice=default_voice or "21m00Tcm4TlvDq8ikWAM",
            base_url=base_url,
        )

    if provider == "local":
        if not db:
            raise ValueError("db is required for local provider")
        if not model_id:
            raise ValueError("model_id is required for local provider")
        return create_local_model_tts_provider(
            db=db,
            model_id=model_id,
        )

    if provider == "mock":
        return MockTTSProvider(
            default_voice=default_voice or "mock_voice_1",
        )

    raise ValueError(f"Unknown provider: {provider}")


__all__ = [
    "OpenAITTSProvider",
    "ElevenLabsTTSProvider",
    "MockTTSProvider",
    "create_tts_provider",
]
