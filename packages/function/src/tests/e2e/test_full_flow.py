"""
E2E Tests - Full System Flow

Tests complete end-to-end voice chat flow:
1. Audio input → STT
2. Text → Chat Engine
3. Response → TTS
4. Audio output
"""

import asyncio
import base64

import pytest

from toolbox.engines.voice_chat import VoiceChatEngine
from toolbox.engines.voice import VoiceEngine


@pytest.mark.asyncio
async def test_full_voice_chat_flow(voice_engine: VoiceEngine, sample_audio_bytes: bytes):
    """Test complete voice chat flow."""
    class MockChatEngine:
        async def send_message(self, conversation_id, user_id, content, **kwargs):
            return {
                "id": "msg_123",
                "conversation_id": conversation_id,
                "role": "assistant",
                "content": f"AI response to: {content}",
                "tokens": len(content),
                "metadata": {},
                "created_at": "2026-01-30T00:00:00Z",
            }, None
    
    chat_engine = MockChatEngine()
    voice_chat = VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )
    
    # Full flow: audio -> text -> chat -> audio
    result = await voice_chat.process_message(
        conversation_id="e2e_test",
        user_id="test_user",
        audio_data=sample_audio_bytes,
        audio_format="wav",
        language="en",
    )
    
    # Verify all steps completed
    assert result is not None
    assert "user_transcript" in result
    assert "assistant_text" in result
    assert "assistant_audio" in result
    
    # Verify transcript
    assert len(result["user_transcript"]) > 0
    
    # Verify response
    assert len(result["assistant_text"]) > 0
    assert "AI response" in result["assistant_text"]
    
    # Verify audio
    assert result["assistant_audio"] is not None
    assert isinstance(result["assistant_audio"], bytes)
    assert len(result["assistant_audio"]) > 0


@pytest.mark.asyncio
async def test_text_only_flow(voice_engine: VoiceEngine):
    """Test text-only flow (no STT)."""
    class MockChatEngine:
        async def send_message(self, conversation_id, user_id, content, **kwargs):
            return {
                "id": "msg_123",
                "conversation_id": conversation_id,
                "role": "assistant",
                "content": f"Response: {content}",
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
        conversation_id="e2e_test",
        user_id="test_user",
        text="Hello, text test",
        voice="test_voice",
    )
    
    assert result is not None
    assert "assistant_text" in result
    assert "assistant_audio_base64" in result
    
    # Decode audio
    audio_bytes = base64.b64decode(result["assistant_audio_base64"])
    assert len(audio_bytes) > 0


@pytest.mark.asyncio
async def test_conversation_context(voice_engine: VoiceEngine):
    """Test that conversation context is maintained."""
    class MockChatEngine:
        def __init__(self):
            self.messages = []
        
        async def send_message(self, conversation_id, user_id, content, **kwargs):
            self.messages.append(content)
            return {
                "id": f"msg_{len(self.messages)}",
                "conversation_id": conversation_id,
                "role": "assistant",
                "content": f"Response {len(self.messages)} to: {content}",
                "tokens": len(content),
                "metadata": {},
                "created_at": "2026-01-30T00:00:00Z",
            }, None
    
    chat_engine = MockChatEngine()
    voice_chat = VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )
    
    # Send multiple messages
    for i in range(3):
        result = await voice_chat.process_text_only(
            conversation_id="context_test",
            user_id="test_user",
            text=f"Message {i}",
            voice="test_voice",
        )
        assert result is not None
    
    # Verify all messages were sent
    assert len(chat_engine.messages) == 3


__all__ = []
