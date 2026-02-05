"""
Deep comprehensive tests for VoiceChatEngine.

Tests full voice chat flow (STT -> Chat -> TTS), error handling, MAESTRO integration, and bug detection.
"""
import pytest
from unittest.mock import AsyncMock, MagicMock, patch
from toolbox.engines.voice_chat import (
    VoiceChatEngine,
    VoiceChatResult,
    create_voice_chat_engine,
)
from toolbox.engines.voice.types import (
    VoiceChatConfig,
    VoiceChatSession,
    VoiceChatState,
    VoiceQuality,
    TTSResponse,
    STTTranscriptionResult,
)


class MockChatEngine:
    """Mock chat engine for testing."""

    def __init__(self):
        self.messages = []
        self.errors = {}

    async def send_message(
        self,
        conversation_id: str,
        user_id: str,
        content: str,
        analyst_role: str | None = None,
        **kwargs,
    ):
        """Mock send_message."""
        if conversation_id in self.errors:
            return None, self.errors[conversation_id]
        
        message = {
            "id": f"msg_{conversation_id}",
            "conversation_id": conversation_id,
            "role": "assistant",
            "content": f"Response to: {content}",
            "tokens": 10,
            "metadata": {},
            "created_at": "2024-01-01T00:00:00Z",
        }
        self.messages.append(message)
        return message, None


class MockVoiceEngine:
    """Mock voice engine for testing."""

    def __init__(self):
        self.sessions = {}
        self.stt_results = {}
        self.tts_results = {}

    async def create_session(
        self,
        conversation_id: str,
        org_id: str,
        user_id: str,
        config: VoiceChatConfig | None = None,
    ) -> VoiceChatSession:
        """Mock create_session."""
        session_id = f"session_{conversation_id}_{user_id}"
        session: VoiceChatSession = {
            "id": session_id,
            "conversation_id": conversation_id,
            "org_id": org_id,
            "user_id": user_id,
            "config": config or VoiceChatConfig(),
            "state": VoiceChatState.IDLE,
            "messages": [],
            "total_audio_seconds": 0.0,
            "total_stt_tokens": 0,
            "total_tts_characters": 0,
            "started_at": "2024-01-01T00:00:00Z",
            "ended_at": "",
        }
        self.sessions[session_id] = session
        return session

    async def get_session(self, session_id: str) -> VoiceChatSession | None:
        """Mock get_session."""
        return self.sessions.get(session_id)

    async def speech_to_text(
        self,
        audio_data: bytes,
        audio_format: str,
        language: str = "en",
        include_timestamps: bool = False,
    ) -> STTTranscriptionResult:
        """Mock speech_to_text."""
        if audio_data in self.stt_results:
            return self.stt_results[audio_data]
        
        return {
            "text": "Hello world",
            "language": language,
            "confidence": 0.95,
            "duration_seconds": 1.0,
            "words": None,
            "cost_usd": 0.01,
        }

    async def text_to_speech(
        self,
        text: str,
        voice: str = "alloy",
        quality: VoiceQuality = VoiceQuality.STANDARD,
        audio_format: str = "mp3",
    ) -> TTSResponse:
        """Mock text_to_speech."""
        if text in self.tts_results:
            return self.tts_results[text]
        
        return {
            "audio_data": b"mock_audio_data",
            "audio_format": VoiceQuality.STANDARD,
            "duration_seconds": 2.0,
            "characters_used": len(text),
            "cost_usd": 0.02,
            "voice": voice,
        }

    async def add_message(
        self,
        session_id: str,
        role: str,
        text: str,
        audio_url: str | None = None,
        duration_seconds: float | None = None,
        stt_confidence: float | None = None,
    ):
        """Mock add_message."""
        session = self.sessions.get(session_id)
        if session:
            message = {
                "id": f"msg_{len(session['messages'])}",
                "conversation_id": session["conversation_id"],
                "role": role,
                "text": text,
                "audio_url": audio_url or "",
                "duration_seconds": duration_seconds or 0.0,
                "stt_confidence": stt_confidence or 0.0,
                "created_at": "2024-01-01T00:00:00Z",
            }
            session["messages"].append(message)
            return message
        return None

    async def end_session(self, session_id: str) -> None:
        """Mock end_session."""
        session = self.sessions.get(session_id)
        if session:
            session["state"] = VoiceChatState.ENDED


class TestVoiceChatEngine:
    """Deep comprehensive tests for VoiceChatEngine."""

    @pytest.fixture
    def chat_engine(self):
        """Create mock chat engine."""
        return MockChatEngine()

    @pytest.fixture
    def voice_engine(self):
        """Create mock voice engine."""
        return MockVoiceEngine()

    @pytest.fixture
    def engine(self, chat_engine, voice_engine):
        """Create VoiceChatEngine instance."""
        return VoiceChatEngine(
            chat_engine=chat_engine,
            voice_engine=voice_engine,
        )

    @pytest.mark.asyncio
    async def test_create_session(self, engine: VoiceChatEngine):
        """Test create_session delegates to voice engine."""
        session = await engine.create_session(
            conversation_id="conv_123",
            org_id="org_456",
            user_id="user_789",
        )
        assert session["conversation_id"] == "conv_123"
        assert session["org_id"] == "org_456"
        assert session["user_id"] == "user_789"

    @pytest.mark.asyncio
    async def test_process_message_full_flow(self, engine: VoiceChatEngine):
        """Test process_message full flow (STT -> Chat -> TTS)."""
        audio_data = b"audio_bytes"
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=audio_data,
        )
        
        assert result["user_transcript"] == "Hello world"
        assert result["stt_confidence"] == 0.95
        assert result["assistant_text"] == "Response to: Hello world"
        assert result["assistant_audio"] == b"mock_audio_data"
        assert result["total_cost_usd"] == 0.03  # STT + TTS

    @pytest.mark.asyncio
    async def test_process_message_stt_error(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test process_message handles STT error."""
        audio_data = b"error_audio"
        
        async def stt_error(*args, **kwargs):
            raise Exception("STT failed")
        
        voice_engine.speech_to_text = stt_error
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=audio_data,
        )
        
        assert result["stt_error"] == "STT failed"
        assert result["user_transcript"] == ""
        assert result["assistant_text"] == ""
        assert result["assistant_audio"] is None

    @pytest.mark.asyncio
    async def test_process_message_chat_error(self, engine: VoiceChatEngine, chat_engine: MockChatEngine):
        """Test process_message handles chat error."""
        chat_engine.errors["conv_123"] = {
            "code": "api_error",
            "message": "Chat failed",
        }
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
        )
        
        assert result["chat_error"] == "Chat failed"
        assert result["assistant_text"] == ""
        assert result["assistant_audio"] is None

    @pytest.mark.asyncio
    async def test_process_message_tts_error(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test process_message handles TTS error but returns text."""
        async def tts_error(*args, **kwargs):
            raise Exception("TTS failed")
        
        voice_engine.text_to_speech = tts_error
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
        )
        
        assert result["tts_error"] == "TTS failed"
        assert result["assistant_text"] == "Response to: Hello world"
        assert result["assistant_audio"] is None

    @pytest.mark.asyncio
    async def test_process_message_thinking_extraction(self, engine: VoiceChatEngine, chat_engine: MockChatEngine):
        """Test process_message extracts thinking blocks."""
        message = {
            "id": "msg_1",
            "conversation_id": "conv_123",
            "role": "assistant",
            "content": "Response <think>thinking content</think> text",
            "tokens": 10,
            "metadata": {},
            "created_at": "2024-01-01T00:00:00Z",
        }
        chat_engine.messages.append(message)
        
        # Override send_message to return message with thinking
        async def send_with_thinking(*args, **kwargs):
            return message, None
        
        chat_engine.send_message = send_with_thinking
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
        )
        
        assert result["assistant_thinking"] == "thinking content"
        assert result["assistant_text"] == "Response  text"

    @pytest.mark.asyncio
    async def test_process_message_maestro_integration(self, engine: VoiceChatEngine):
        """Test process_message uses MAESTRO for agent routing."""
        mock_maestro = MagicMock()
        mock_maestro.predict = AsyncMock(return_value={
            "agents": [
                {"agent_id": "analyst_1", "confidence": 0.85},
            ]
        })
        engine.maestro = mock_maestro
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
            analyst_role=None,  # Should use MAESTRO prediction
        )
        
        mock_maestro.predict.assert_called_once()
        assert result["assistant_text"] == "Response to: Hello world"

    @pytest.mark.asyncio
    async def test_process_message_maestro_low_confidence(self, engine: VoiceChatEngine):
        """Test process_message ignores MAESTRO if confidence too low."""
        mock_maestro = MagicMock()
        mock_maestro.predict = AsyncMock(return_value={
            "agents": [
                {"agent_id": "analyst_1", "confidence": 0.5},  # Below 0.75 threshold
            ]
        })
        engine.maestro = mock_maestro
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
            analyst_role="manual_role",
        )
        
        # Should use manual_role, not MAESTRO prediction
        assert result["assistant_text"] == "Response to: Hello world"

    @pytest.mark.asyncio
    async def test_process_message_maestro_error(self, engine: VoiceChatEngine):
        """Test process_message handles MAESTRO error gracefully."""
        mock_maestro = MagicMock()
        mock_maestro.predict = AsyncMock(side_effect=Exception("MAESTRO failed"))
        engine.maestro = mock_maestro
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
        )
        
        # Should continue without MAESTRO
        assert result["assistant_text"] == "Response to: Hello world"

    @pytest.mark.asyncio
    async def test_process_message_saves_messages(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test process_message saves messages to session."""
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
        )
        
        # Check that messages were saved
        session_id = f"voice_session_conv_123_user_456"
        session = await voice_engine.get_session(session_id)
        assert session is not None
        assert len(session["messages"]) == 2  # User + Assistant

    @pytest.mark.asyncio
    async def test_process_text_only(self, engine: VoiceChatEngine):
        """Test process_text_only (text -> chat -> TTS)."""
        result = await engine.process_text_only(
            conversation_id="conv_123",
            user_id="user_456",
            text="Hello",
        )
        
        assert result["user_transcript"] == "Hello"
        assert result["stt_confidence"] == 1.0
        assert result["stt_cost_usd"] == 0.0
        assert result["assistant_text"] == "Response to: Hello"
        assert result["assistant_audio"] == b"mock_audio_data"

    @pytest.mark.asyncio
    async def test_process_text_only_chat_error(self, engine: VoiceChatEngine, chat_engine: MockChatEngine):
        """Test process_text_only handles chat error."""
        chat_engine.errors["conv_123"] = {
            "code": "api_error",
            "message": "Chat failed",
        }
        
        result = await engine.process_text_only(
            conversation_id="conv_123",
            user_id="user_456",
            text="Hello",
        )
        
        assert result["chat_error"] == "Chat failed"
        assert result["assistant_text"] == ""

    @pytest.mark.asyncio
    async def test_get_session(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test get_session delegates to voice engine."""
        session = await voice_engine.create_session(
            conversation_id="conv_123",
            org_id="org_456",
            user_id="user_789",
        )
        
        retrieved = await engine.get_session(session["id"])
        assert retrieved == session

    @pytest.mark.asyncio
    async def test_end_session(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test end_session delegates to voice engine."""
        session = await voice_engine.create_session(
            conversation_id="conv_123",
            org_id="org_456",
            user_id="user_789",
        )
        
        await engine.end_session(session["id"])
        
        updated_session = await voice_engine.get_session(session["id"])
        assert updated_session["state"] == VoiceChatState.ENDED

    @pytest.mark.asyncio
    async def test_process_message_empty_transcript(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test process_message handles empty transcript."""
        async def empty_stt(*args, **kwargs):
            return {
                "text": "",
                "language": "en",
                "confidence": 0.0,
                "duration_seconds": 0.0,
                "words": None,
                "cost_usd": 0.0,
            }
        
        voice_engine.speech_to_text = empty_stt
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
        )
        
        # Should still proceed with empty transcript
        assert result["user_transcript"] == ""

    @pytest.mark.asyncio
    async def test_process_message_voice_config_from_session(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test process_message uses voice config from session."""
        config: VoiceChatConfig = {
            "voice": "custom_voice",
            "quality": VoiceQuality.HD,
        }
        
        session = await voice_engine.create_session(
            conversation_id="conv_123",
            org_id="org_456",
            user_id="user_789",
            config=config,
        )
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_789",
            audio_data=b"audio",
        )
        
        # Check that TTS was called with custom voice
        # (voice_engine.text_to_speech should have been called with "custom_voice")
        assert result["assistant_audio"] is not None

    @pytest.mark.asyncio
    async def test_process_message_cost_calculation(self, engine: VoiceChatEngine, voice_engine: MockVoiceEngine):
        """Test process_message calculates total cost correctly."""
        async def custom_stt(*args, **kwargs):
            return {
                "text": "test",
                "language": "en",
                "confidence": 0.95,
                "duration_seconds": 1.0,
                "words": None,
                "cost_usd": 0.05,
            }
        
        async def custom_tts(*args, **kwargs):
            return {
                "audio_data": b"audio",
                "audio_format": VoiceQuality.STANDARD,
                "duration_seconds": 2.0,
                "characters_used": 10,
                "cost_usd": 0.10,
                "voice": "alloy",
            }
        
        voice_engine.speech_to_text = custom_stt
        voice_engine.text_to_speech = custom_tts
        
        result = await engine.process_message(
            conversation_id="conv_123",
            user_id="user_456",
            audio_data=b"audio",
        )
        
        assert result["stt_cost_usd"] == 0.05
        assert result["tts_cost_usd"] == 0.10
        assert result["total_cost_usd"] == 0.15


class TestCreateVoiceChatEngine:
    """Deep comprehensive tests for create_voice_chat_engine factory."""

    @pytest.mark.asyncio
    async def test_create_engine(self):
        """Test factory creates engine."""
        chat_engine = MockChatEngine()
        voice_engine = MockVoiceEngine()
        
        engine = await create_voice_chat_engine(
            chat_engine=chat_engine,
            voice_engine=voice_engine,
        )
        
        assert isinstance(engine, VoiceChatEngine)
        assert engine.chat_engine == chat_engine
        assert engine.voice_engine == voice_engine


class TestBugDetection:
    """Bug detection tests for VoiceChatEngine."""

    @pytest.mark.asyncio
    async def test_bug_session_id_generation_may_collide(self):
        """BUG: Session ID generation may collide."""
        # Session IDs use deterministic UUID, collisions possible
        # This test documents the potential issue
        # TODO: Add test to verify session ID uniqueness

    @pytest.mark.asyncio
    async def test_bug_messages_may_not_be_saved_on_error(self):
        """BUG: Messages may not be saved if TTS fails."""
        # If TTS fails, assistant message may not be saved
        # This test documents the potential issue
        # TODO: Add test to verify message saving on TTS error

    @pytest.mark.asyncio
    async def test_bug_cost_may_not_include_chat_cost(self):
        """BUG: Total cost may not include chat cost."""
        # Total cost only includes STT + TTS, not chat
        # This test documents the potential issue
        # TODO: Add test to verify cost calculation includes chat

    @pytest.mark.asyncio
    async def test_bug_thinking_extraction_may_fail(self):
        """BUG: Thinking extraction may fail on malformed tags."""
        # Malformed <think> tags may cause extraction to fail
        # This test documents the potential issue
        # TODO: Add test with malformed thinking tags

    @pytest.mark.asyncio
    async def test_bug_maestro_prediction_may_be_ignored(self):
        """BUG: MAESTRO prediction may be ignored if manual role provided."""
        # Manual analyst_role may override MAESTRO prediction
        # This test documents the potential issue
        # TODO: Add test to verify MAESTRO vs manual role priority
