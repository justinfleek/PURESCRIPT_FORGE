"""
Unit Tests - Voice Engine

Tests voice engine components in isolation.
"""

import pytest

from toolbox.engines.voice import VoiceEngine, VoiceQuality
from toolbox.engines.voice.types import VoiceChatConfig, VoiceChatMessage


@pytest.mark.asyncio
async def test_voice_engine_creation(voice_engine: VoiceEngine):
    """Test voice engine can be created."""
    assert voice_engine is not None
    assert voice_engine.default_voice == "test_voice"
    assert voice_engine.default_language == "en"


@pytest.mark.asyncio
async def test_text_to_speech(voice_engine: VoiceEngine):
    """Test text-to-speech synthesis."""
    text = "Hello, this is a test"
    audio = await voice_engine.text_to_speech(
        text=text,
        voice="test_voice",
        quality=VoiceQuality.STANDARD,
    )
    
    assert audio is not None
    assert "audio_data" in audio
    assert isinstance(audio["audio_data"], bytes)
    assert len(audio["audio_data"]) > 0


@pytest.mark.asyncio
async def test_speech_to_text(voice_engine: VoiceEngine, sample_audio_bytes: bytes):
    """Test speech-to-text transcription."""
    result = await voice_engine.speech_to_text(
        audio_data=sample_audio_bytes,
        audio_format="wav",
        language="en",
    )
    
    assert result is not None
    assert "text" in result
    assert isinstance(result["text"], str)
    assert len(result["text"]) > 0


@pytest.mark.asyncio
async def test_create_session(voice_engine: VoiceEngine):
    """Test voice session creation."""
    session = await voice_engine.create_session(
        conversation_id="test_conv",
        org_id="test_org",
        user_id="test_user",
    )
    
    assert session is not None
    assert session.conversation_id == "test_conv"
    assert session.org_id == "test_org"
    assert session.user_id == "test_user"
    assert session.state == "idle"


@pytest.mark.asyncio
async def test_get_session(voice_engine: VoiceEngine):
    """Test retrieving voice session."""
    # Create session
    created = await voice_engine.create_session(
        conversation_id="test_conv",
        org_id="test_org",
        user_id="test_user",
    )
    
    # Retrieve session
    retrieved = await voice_engine.get_session(created.id)
    
    assert retrieved is not None
    assert retrieved.id == created.id
    assert retrieved.conversation_id == "test_conv"


__all__ = []
