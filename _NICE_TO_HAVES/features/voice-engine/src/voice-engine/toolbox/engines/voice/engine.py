"""
Voice Engine - Main VoiceEngine class implementation.

This module contains the VoiceEngine class for TTS, STT, and voice chat.
"""

from __future__ import annotations

import logging
from datetime import timezone, datetime
from typing import Literal

from .protocols import STTProviderProtocol, TTSProviderProtocol, VoiceDatabaseProtocol
from .session_ops import (
    get_session_messages,
    get_session_row,
    row_to_session,
    save_message,
    save_session,
    update_session_audio_seconds,
    update_session_state,
    update_session_tts_characters,
)
from .types import (
    AudioFormat,
    STTTranscriptionResult,
    TTSResponse,
    VoiceChatConfig,
    VoiceChatMessage,
    VoiceChatMode,
    VoiceChatSession,
    VoiceChatState,
    VoiceQuality,
    _str_from_db,
)


logger = logging.getLogger(__name__)


# =============================================================================
# Voice Engine
# =============================================================================


class VoiceEngine:
    """
    Voice engine for TTS, STT, and voice chat.

    Features:
    - Multi-provider support (OpenAI, ElevenLabs, etc.)
    - Voice persona management
    - Voice chat session management
    - Cost tracking
    - Deterministic behavior

    Usage:
        engine = VoiceEngine(db=db, tts_provider=tts, stt_provider=stt)
        await engine.init_tables()

        # Text to speech
        audio = await engine.text_to_speech("Hello", voice="alloy")

        # Speech to text
        text = await engine.speech_to_text(audio_data)

        # Voice chat
        session = await engine.create_session(
            conversation_id="conv_123",
            user_id="user_456",
            config={"voice": "alloy", "mode": "push_to_talk"}
        )
    """

    def __init__(
        self,
        db: VoiceDatabaseProtocol,
        tts_provider: TTSProviderProtocol,
        stt_provider: STTProviderProtocol,
        default_voice: str = "alloy",
        default_language: str = "en",
    ) -> None:
        """
        Initialize voice engine.

        Args:
            db: Database connection implementing VoiceDatabaseProtocol
            tts_provider: TTS provider implementation
            stt_provider: STT provider implementation
            default_voice: Default voice ID
            default_language: Default language code
        """
        self.db = db
        self.tts_provider = tts_provider
        self.stt_provider = stt_provider
        self.default_voice = default_voice
        self.default_language = default_language

    async def text_to_speech(
        self,
        text: str,
        voice: str | None = None,
        model: str | None = None,
        speed: float = 1.0,
        quality: VoiceQuality = VoiceQuality.STANDARD,
        audio_format: AudioFormat = AudioFormat.MP3,
    ) -> TTSResponse:
        """
        Convert text to speech.

        Args:
            text: Text to synthesize (1-4096 chars)
            voice: Voice ID (uses default if None)
            model: Model ID (provider-specific)
            speed: Speed multiplier (0.25-4.0)
            quality: Voice quality level
            audio_format: Output audio format

        Returns:
            TTS response with audio data

        Raises:
            ValueError: If text is empty or too long
        """
        voice = voice or self.default_voice

        # Validate text length
        if not text:
            raise ValueError("Text cannot be empty")
        if len(text) > 4096:
            raise ValueError(f"Text too long: {len(text)} chars (max 4096)")

        # Validate speed
        if not (0.25 <= speed <= 4.0):
            raise ValueError(f"Speed must be in [0.25, 4.0], got {speed}")

        # Synthesize
        audio_data = await self.tts_provider.synthesize(
            text=text,
            voice=voice,
            model=model,
            speed=speed,
            format=audio_format.value,
        )

        # Estimate duration (rough: 150 words per minute, avg word 5 chars)
        estimated_duration = (len(text) / 5) / 150 * 60

        # Calculate cost
        cost = self.tts_provider.estimate_cost(text, model)

        return TTSResponse(
            audio_data=audio_data,
            audio_format=audio_format,
            duration_seconds=estimated_duration,
            characters_used=len(text),
            cost_usd=cost,
            voice=voice,
        )

    async def speech_to_text(
        self,
        audio_data: bytes,
        audio_format: Literal["mp3", "wav", "ogg", "flac", "webm", "m4a"],
        language: str = "en",
        include_timestamps: bool = False,
    ) -> STTTranscriptionResult:
        """
        Convert speech to text.

        Args:
            audio_data: Raw audio bytes (max 25MB)
            audio_format: Audio format
            language: ISO 639-1 language code
            include_timestamps: Include word-level timestamps

        Returns:
            STT transcription result

        Raises:
            ValueError: If audio is empty or too large
        """
        # Validate audio size
        if not audio_data:
            raise ValueError("Audio data cannot be empty")
        if len(audio_data) > 25 * 1024 * 1024:
            raise ValueError(f"Audio too large: {len(audio_data)} bytes (max 25MB)")

        # Transcribe
        result = await self.stt_provider.transcribe(
            audio_data=audio_data,
            audio_format=audio_format,
            language=language,
            include_timestamps=include_timestamps,
        )

        return result

    async def create_session(
        self,
        conversation_id: str,
        org_id: str,
        user_id: str,
        config: VoiceChatConfig | None = None,
    ) -> VoiceChatSession:
        """
        Create a voice chat session.

        Args:
            conversation_id: Conversation ID
            org_id: Organization ID
            user_id: User ID
            config: Voice chat configuration

        Returns:
            Voice chat session
        """
        from toolbox.core.deterministic_id import make_uuid

        session_id = make_uuid("voice_session", conversation_id, user_id)

        # Default config
        if config is None:
            config = VoiceChatConfig(
                voice=self.default_voice,
                quality=VoiceQuality.STANDARD,
                mode=VoiceChatMode.PUSH_TO_TALK,
                language=self.default_language,
                speed=1.0,
                vad_threshold=0.5,
                silence_timeout_ms=2000,
                max_duration_seconds=300,
                interrupt_enabled=True,
            )

        now = datetime.now(timezone.utc).isoformat()

        # Save to database
        await save_session(
            db=self.db,
            session_id=session_id,
            conversation_id=conversation_id,
            org_id=org_id,
            user_id=user_id,
            config=config,
            state=VoiceChatState.IDLE,
            started_at=now,
        )

        return VoiceChatSession(
            id=session_id,
            conversation_id=conversation_id,
            org_id=org_id,
            user_id=user_id,
            config=config,
            state=VoiceChatState.IDLE,
            messages=[],
            total_audio_seconds=0.0,
            total_stt_tokens=0,
            total_tts_characters=0,
            started_at=now,
            ended_at=None,
        )

    async def add_message(
        self,
        session_id: str,
        role: Literal["user", "assistant"],
        text: str,
        audio_url: str | None = None,
        duration_seconds: float | None = None,
        stt_confidence: float | None = None,
    ) -> VoiceChatMessage:
        """
        Add a message to a voice chat session.

        Args:
            session_id: Voice chat session ID
            role: Message role
            text: Message text
            audio_url: URL to audio file
            duration_seconds: Audio duration
            stt_confidence: STT confidence (for user messages)

        Returns:
            Voice chat message
        """
        from toolbox.core.deterministic_id import make_uuid

        message_id = make_uuid("voice_msg", session_id, role, text[:50])

        # Get conversation ID from session
        session = await get_session_row(self.db, session_id)
        raw_conv_id = session.get("conversation_id") if session else ""
        conversation_id = _str_from_db(raw_conv_id)

        now = datetime.now(timezone.utc).isoformat()

        # Save to database
        await save_message(
            db=self.db,
            message_id=message_id,
            session_id=session_id,
            conversation_id=conversation_id,
            role=role,
            text=text,
            audio_url=audio_url,
            duration_seconds=duration_seconds,
            stt_confidence=stt_confidence,
            created_at=now,
        )

        # Update session totals
        if role == "user" and duration_seconds:
            await update_session_audio_seconds(self.db, session_id, duration_seconds)

        if role == "assistant" and text:
            await update_session_tts_characters(self.db, session_id, len(text))

        return VoiceChatMessage(
            id=message_id,
            conversation_id=conversation_id,
            role=role,
            text=text,
            audio_url=audio_url,
            duration_seconds=duration_seconds,
            stt_confidence=stt_confidence,
            created_at=now,
        )

    async def get_session(self, session_id: str) -> VoiceChatSession | None:
        """
        Get a voice chat session.

        Args:
            session_id: Session ID

        Returns:
            Voice chat session or None
        """
        session_row = await get_session_row(self.db, session_id)
        if not session_row:
            return None

        # Get messages
        messages = await get_session_messages(self.db, session_id)

        return row_to_session(session_row, messages)

    async def end_session(self, session_id: str) -> None:
        """
        End a voice chat session.

        Args:
            session_id: Session ID
        """
        now = datetime.now(timezone.utc).isoformat()
        await update_session_state(self.db, session_id, VoiceChatState.ENDED, now)


# =============================================================================
# Factory Functions
# =============================================================================


async def create_voice_engine(
    db: VoiceDatabaseProtocol,
    tts_provider: TTSProviderProtocol,
    stt_provider: STTProviderProtocol,
    default_voice: str = "alloy",
) -> VoiceEngine:
    """
    Factory function to create voice engine.

    Args:
        db: Database connection
        tts_provider: TTS provider implementation
        stt_provider: STT provider implementation
        default_voice: Default voice ID

    Returns:
        Configured VoiceEngine instance
    """
    return VoiceEngine(
        db=db,
        tts_provider=tts_provider,
        stt_provider=stt_provider,
        default_voice=default_voice,
    )


# =============================================================================
# Exports
# =============================================================================

__all__ = [
    "VoiceEngine",
    "create_voice_engine",
]
