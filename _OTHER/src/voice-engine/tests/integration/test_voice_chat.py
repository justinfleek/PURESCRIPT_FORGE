"""
Integration Tests - Voice Chat Engine

Tests component interactions and integration points.
"""

import pytest

from toolbox.engines.voice_chat import VoiceChatEngine
from toolbox.engines.chatbot import VeniceChatEngine


@pytest.mark.asyncio
async def test_voice_chat_creation(voice_engine, test_db):
    """Test voice chat engine can be created."""
    # Create mock chat engine
    class MockChatEngine:
        async def send_message(self, conversation_id, user_id, content, **kwargs):
            return {
                "id": "msg_123",
                "conversation_id": conversation_id,
                "role": "assistant",
                "content": f"Echo: {content}",
                "tokens": len(content),
                "metadata": {},
                "created_at": "2026-01-30T00:00:00Z",
            }, None
    
    chat_engine = MockChatEngine()
    voice_chat = VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )
    
    assert voice_chat is not None
    assert voice_chat.chat_engine == chat_engine
    assert voice_chat.voice_engine == voice_engine


@pytest.mark.asyncio
async def test_voice_chat_text_flow(voice_engine, test_db):
    """Test text-only voice chat flow."""
    class MockChatEngine:
        async def send_message(self, conversation_id, user_id, content, **kwargs):
            return {
                "id": "msg_123",
                "conversation_id": conversation_id,
                "role": "assistant",
                "content": f"Response to: {content}",
                "tokens": len(content),
                "metadata": {},
                "created_at": "2026-01-30T00:00:00Z",
            }, None
    
    chat_engine = MockChatEngine()
    voice_chat = VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )
    
    result = await voice_chat.process_text_only(
        conversation_id="test_conv",
        user_id="test_user",
        text="Hello test",
        voice="test_voice",
    )
    
    assert result is not None
    assert "assistant_text" in result
    assert "assistant_audio_base64" in result
    assert len(result["assistant_text"]) > 0


@pytest.mark.asyncio
async def test_voice_chat_full_flow(voice_engine, test_db, sample_audio_bytes):
    """Test full voice chat flow (audio -> text -> chat -> audio)."""
    class MockChatEngine:
        async def send_message(self, conversation_id, user_id, content, **kwargs):
            return {
                "id": "msg_123",
                "conversation_id": conversation_id,
                "role": "assistant",
                "content": f"Response to: {content}",
                "tokens": len(content),
                "metadata": {},
                "created_at": "2026-01-30T00:00:00Z",
            }, None
    
    chat_engine = MockChatEngine()
    voice_chat = VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )
    
    result = await voice_chat.process_message(
        conversation_id="test_conv",
        user_id="test_user",
        audio_data=sample_audio_bytes,
        audio_format="wav",
        language="en",
    )
    
    assert result is not None
    assert "user_transcript" in result
    assert "assistant_text" in result
    assert "assistant_audio" in result


__all__ = []
