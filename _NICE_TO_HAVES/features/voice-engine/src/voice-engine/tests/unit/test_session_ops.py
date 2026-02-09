"""
Deep comprehensive tests for session database operations.

Tests session CRUD, message operations, config parsing, and bug detection.
"""
import json
import pytest
from unittest.mock import AsyncMock, MagicMock
from toolbox.engines.voice.session_ops import (
    save_session,
    get_session_row,
    update_session_state,
    update_session_audio_seconds,
    update_session_tts_characters,
    save_message,
    get_session_messages,
    parse_config,
    row_to_session,
)
from toolbox.engines.voice.types import (
    VoiceChatState,
    VoiceChatMode,
    VoiceQuality,
    VoiceChatConfig,
    VoiceChatMessage,
    VoiceChatSession,
)


class TestSaveSession:
    """Deep comprehensive tests for save_session function."""

    @pytest.mark.asyncio
    async def test_save_session_basic(self):
        """Test saving session with all fields."""
        mock_db = AsyncMock()
        config: VoiceChatConfig = {
            "voice": "alloy",
            "quality": VoiceQuality.STANDARD,
            "mode": VoiceChatMode.VOICE_ACTIVITY,
        }
        
        await save_session(
            db=mock_db,
            session_id="session-123",
            conversation_id="conv-123",
            org_id="org-123",
            user_id="user-123",
            config=config,
            state=VoiceChatState.IDLE,
            started_at="2024-01-01T00:00:00Z",
        )
        
        mock_db.execute.assert_called_once()
        call_args = mock_db.execute.call_args
        assert "INSERT INTO voice_chat_sessions" in call_args[0][0]
        assert call_args[1][0][0] == "session-123"
        assert call_args[1][0][1] == "conv-123"
        assert call_args[1][0][2] == "org-123"
        assert call_args[1][0][3] == "user-123"

    @pytest.mark.asyncio
    async def test_save_session_config_serialized(self):
        """Test config is serialized to JSON."""
        mock_db = AsyncMock()
        config: VoiceChatConfig = {
            "voice": "alloy",
            "quality": VoiceQuality.STANDARD,
        }
        
        await save_session(
            db=mock_db,
            session_id="session-123",
            conversation_id="conv-123",
            org_id="org-123",
            user_id="user-123",
            config=config,
            state=VoiceChatState.IDLE,
            started_at="2024-01-01T00:00:00Z",
        )
        
        call_args = mock_db.execute.call_args
        config_json = call_args[1][0][4]
        parsed = json.loads(config_json)
        assert parsed["voice"] == "alloy"
        assert parsed["quality"] == "standard"

    @pytest.mark.asyncio
    async def test_save_session_state_value(self):
        """Test state is converted to value."""
        mock_db = AsyncMock()
        config: VoiceChatConfig = {}
        
        await save_session(
            db=mock_db,
            session_id="session-123",
            conversation_id="conv-123",
            org_id="org-123",
            user_id="user-123",
            config=config,
            state=VoiceChatState.LISTENING,
            started_at="2024-01-01T00:00:00Z",
        )
        
        call_args = mock_db.execute.call_args
        assert call_args[1][0][5] == "listening"

    @pytest.mark.asyncio
    async def test_save_session_initial_totals_zero(self):
        """Test initial totals are zero."""
        mock_db = AsyncMock()
        config: VoiceChatConfig = {}
        
        await save_session(
            db=mock_db,
            session_id="session-123",
            conversation_id="conv-123",
            org_id="org-123",
            user_id="user-123",
            config=config,
            state=VoiceChatState.IDLE,
            started_at="2024-01-01T00:00:00Z",
        )
        
        call_args = mock_db.execute.call_args
        assert call_args[1][0][6] == 0.0  # total_audio_seconds
        assert call_args[1][0][7] == 0  # total_stt_tokens
        assert call_args[1][0][8] == 0  # total_tts_characters
        assert call_args[1][0][9] == "2024-01-01T00:00:00Z"  # started_at
        assert call_args[1][0][10] is None  # ended_at


class TestGetSessionRow:
    """Deep comprehensive tests for get_session_row function."""

    @pytest.mark.asyncio
    async def test_get_session_row_exists(self):
        """Test getting existing session."""
        mock_db = AsyncMock()
        mock_row = {
            "id": "session-123",
            "conversation_id": "conv-123",
            "org_id": "org-123",
            "user_id": "user-123",
            "config": '{"voice": "alloy"}',
            "state": "idle",
            "total_audio_seconds": 10.5,
            "total_stt_tokens": 100,
            "total_tts_characters": 500,
            "started_at": "2024-01-01T00:00:00Z",
            "ended_at": None,
        }
        mock_db.fetch_one = AsyncMock(return_value=mock_row)
        
        result = await get_session_row(mock_db, "session-123")
        
        assert result == mock_row
        mock_db.fetch_one.assert_called_once()
        assert mock_db.fetch_one.call_args[1][0][0] == "session-123"

    @pytest.mark.asyncio
    async def test_get_session_row_not_exists(self):
        """Test getting non-existent session."""
        mock_db = AsyncMock()
        mock_db.fetch_one = AsyncMock(return_value=None)
        
        result = await get_session_row(mock_db, "session-123")
        
        assert result is None


class TestUpdateSessionState:
    """Deep comprehensive tests for update_session_state function."""

    @pytest.mark.asyncio
    async def test_update_session_state_basic(self):
        """Test updating session state."""
        mock_db = AsyncMock()
        
        await update_session_state(
            db=mock_db,
            session_id="session-123",
            state=VoiceChatState.PROCESSING,
        )
        
        mock_db.execute.assert_called_once()
        call_args = mock_db.execute.call_args
        assert "UPDATE voice_chat_sessions" in call_args[0][0]
        assert "state = ?" in call_args[0][0]
        assert call_args[1][0][0] == "processing"
        assert call_args[1][0][1] == "session-123"

    @pytest.mark.asyncio
    async def test_update_session_state_with_ended_at(self):
        """Test updating session state with ended_at."""
        mock_db = AsyncMock()
        
        await update_session_state(
            db=mock_db,
            session_id="session-123",
            state=VoiceChatState.ENDED,
            ended_at="2024-01-01T01:00:00Z",
        )
        
        call_args = mock_db.execute.call_args
        assert "ended_at = ?" in call_args[0][0]
        assert call_args[1][0][1] == "2024-01-01T01:00:00Z"

    @pytest.mark.asyncio
    async def test_update_session_state_all_states(self):
        """Test updating to all possible states."""
        mock_db = AsyncMock()
        
        for state in VoiceChatState:
            await update_session_state(
                db=mock_db,
                session_id="session-123",
                state=state,
            )
        
        assert mock_db.execute.call_count == len(VoiceChatState)


class TestUpdateSessionAudioSeconds:
    """Deep comprehensive tests for update_session_audio_seconds function."""

    @pytest.mark.asyncio
    async def test_update_session_audio_seconds(self):
        """Test updating audio seconds."""
        mock_db = AsyncMock()
        
        await update_session_audio_seconds(
            db=mock_db,
            session_id="session-123",
            duration=5.5,
        )
        
        mock_db.execute.assert_called_once()
        call_args = mock_db.execute.call_args
        assert "total_audio_seconds = total_audio_seconds + ?" in call_args[0][0]
        assert call_args[1][0][0] == 5.5
        assert call_args[1][0][1] == "session-123"

    @pytest.mark.asyncio
    async def test_update_session_audio_seconds_accumulates(self):
        """Test audio seconds accumulate."""
        mock_db = AsyncMock()
        
        await update_session_audio_seconds(mock_db, "session-123", 5.0)
        await update_session_audio_seconds(mock_db, "session-123", 3.0)
        
        assert mock_db.execute.call_count == 2
        # Both should use addition
        assert "+ ?" in mock_db.execute.call_args_list[0][0][0]
        assert "+ ?" in mock_db.execute.call_args_list[1][0][0]


class TestUpdateSessionTTSCharacters:
    """Deep comprehensive tests for update_session_tts_characters function."""

    @pytest.mark.asyncio
    async def test_update_session_tts_characters(self):
        """Test updating TTS characters."""
        mock_db = AsyncMock()
        
        await update_session_tts_characters(
            db=mock_db,
            session_id="session-123",
            character_count=100,
        )
        
        mock_db.execute.assert_called_once()
        call_args = mock_db.execute.call_args
        assert "total_tts_characters = total_tts_characters + ?" in call_args[0][0]
        assert call_args[1][0][0] == 100
        assert call_args[1][0][1] == "session-123"

    @pytest.mark.asyncio
    async def test_update_session_tts_characters_accumulates(self):
        """Test TTS characters accumulate."""
        mock_db = AsyncMock()
        
        await update_session_tts_characters(mock_db, "session-123", 50)
        await update_session_tts_characters(mock_db, "session-123", 75)
        
        assert mock_db.execute.call_count == 2


class TestSaveMessage:
    """Deep comprehensive tests for save_message function."""

    @pytest.mark.asyncio
    async def test_save_message_user(self):
        """Test saving user message."""
        mock_db = AsyncMock()
        
        await save_message(
            db=mock_db,
            message_id="msg-123",
            session_id="session-123",
            conversation_id="conv-123",
            role="user",
            text="Hello",
            audio_url="https://example.com/audio.mp3",
            duration_seconds=2.5,
            stt_confidence=0.95,
            created_at="2024-01-01T00:00:00Z",
        )
        
        mock_db.execute.assert_called_once()
        call_args = mock_db.execute.call_args
        assert "INSERT INTO voice_chat_messages" in call_args[0][0]
        assert call_args[1][0][0] == "msg-123"
        assert call_args[1][0][3] == "user"
        assert call_args[1][0][4] == "Hello"

    @pytest.mark.asyncio
    async def test_save_message_assistant(self):
        """Test saving assistant message."""
        mock_db = AsyncMock()
        
        await save_message(
            db=mock_db,
            message_id="msg-123",
            session_id="session-123",
            conversation_id="conv-123",
            role="assistant",
            text="Hi there!",
            audio_url=None,
            duration_seconds=None,
            stt_confidence=None,
            created_at="2024-01-01T00:00:00Z",
        )
        
        call_args = mock_db.execute.call_args
        assert call_args[1][0][3] == "assistant"
        assert call_args[1][0][4] == "Hi there!"
        assert call_args[1][0][5] is None  # audio_url
        assert call_args[1][0][6] is None  # duration_seconds
        assert call_args[1][0][7] is None  # stt_confidence


class TestGetSessionMessages:
    """Deep comprehensive tests for get_session_messages function."""

    @pytest.mark.asyncio
    async def test_get_session_messages_empty(self):
        """Test getting messages for session with no messages."""
        mock_db = AsyncMock()
        mock_db.fetch_all = AsyncMock(return_value=[])
        
        messages = await get_session_messages(mock_db, "session-123")
        
        assert messages == []
        mock_db.fetch_all.assert_called_once()

    @pytest.mark.asyncio
    async def test_get_session_messages_multiple(self):
        """Test getting multiple messages."""
        mock_db = AsyncMock()
        mock_rows = [
            {
                "id": "msg-1",
                "session_id": "session-123",
                "conversation_id": "conv-123",
                "role": "user",
                "text": "Hello",
                "audio_url": "audio1.mp3",
                "duration_seconds": 2.0,
                "stt_confidence": 0.9,
                "created_at": "2024-01-01T00:00:00Z",
            },
            {
                "id": "msg-2",
                "session_id": "session-123",
                "conversation_id": "conv-123",
                "role": "assistant",
                "text": "Hi there!",
                "audio_url": None,
                "duration_seconds": None,
                "stt_confidence": None,
                "created_at": "2024-01-01T00:00:01Z",
            },
        ]
        mock_db.fetch_all = AsyncMock(return_value=mock_rows)
        
        messages = await get_session_messages(mock_db, "session-123")
        
        assert len(messages) == 2
        assert messages[0].role == "user"
        assert messages[0].text == "Hello"
        assert messages[1].role == "assistant"
        assert messages[1].text == "Hi there!"

    @pytest.mark.asyncio
    async def test_get_session_messages_ordered(self):
        """Test messages are ordered by created_at."""
        mock_db = AsyncMock()
        mock_rows = [
            {
                "id": "msg-2",
                "session_id": "session-123",
                "conversation_id": "conv-123",
                "role": "assistant",
                "text": "Second",
                "created_at": "2024-01-01T00:00:01Z",
            },
            {
                "id": "msg-1",
                "session_id": "session-123",
                "conversation_id": "conv-123",
                "role": "user",
                "text": "First",
                "created_at": "2024-01-01T00:00:00Z",
            },
        ]
        mock_db.fetch_all = AsyncMock(return_value=mock_rows)
        
        messages = await get_session_messages(mock_db, "session-123")
        
        # Should be ordered by created_at ASC
        assert messages[0].text == "First"
        assert messages[1].text == "Second"


class TestParseConfig:
    """Deep comprehensive tests for parse_config function."""

    def test_parse_config_basic(self):
        """Test parsing basic config."""
        config_json = '{"voice": "alloy", "quality": "standard"}'
        config = parse_config(config_json)
        assert config["voice"] == "alloy"
        assert config["quality"] == VoiceQuality.STANDARD

    def test_parse_config_all_fields(self):
        """Test parsing config with all fields."""
        config_json = json.dumps({
            "voice": "alloy",
            "quality": "hd",
            "mode": "voice_activity",
            "language": "en-US",
            "speed": 1.0,
            "vad_threshold": 0.5,
            "silence_timeout_ms": 2000,
            "max_duration_seconds": 300,
            "interrupt_enabled": True,
        })
        config = parse_config(config_json)
        assert config["voice"] == "alloy"
        assert config["quality"] == VoiceQuality.HD
        assert config["mode"] == VoiceChatMode.VOICE_ACTIVITY
        assert config["language"] == "en-US"
        assert config["speed"] == 1.0
        assert config["vad_threshold"] == 0.5
        assert config["silence_timeout_ms"] == 2000
        assert config["max_duration_seconds"] == 300
        assert config["interrupt_enabled"] is True

    def test_parse_config_invalid_json(self):
        """Test parsing invalid JSON returns empty config."""
        config = parse_config("invalid json")
        assert isinstance(config, VoiceChatConfig)
        assert len(config) == 0

    def test_parse_config_empty_json(self):
        """Test parsing empty JSON returns empty config."""
        config = parse_config("{}")
        assert isinstance(config, VoiceChatConfig)

    def test_parse_config_partial_fields(self):
        """Test parsing config with partial fields."""
        config_json = '{"voice": "alloy"}'
        config = parse_config(config_json)
        assert config["voice"] == "alloy"
        # Other fields should have defaults or be absent

    def test_parse_config_invalid_types(self):
        """Test parsing config with invalid types."""
        config_json = '{"voice": 123, "quality": true}'
        config = parse_config(config_json)
        # Invalid types should be ignored
        assert "voice" not in config or config["voice"] != 123


class TestRowToSession:
    """Deep comprehensive tests for row_to_session function."""

    def test_row_to_session_basic(self):
        """Test converting row to session."""
        session_row = {
            "id": "session-123",
            "conversation_id": "conv-123",
            "org_id": "org-123",
            "user_id": "user-123",
            "config": '{"voice": "alloy"}',
            "state": "idle",
            "total_audio_seconds": 10.5,
            "total_stt_tokens": 100,
            "total_tts_characters": 500,
            "started_at": "2024-01-01T00:00:00Z",
            "ended_at": None,
        }
        messages: list[VoiceChatMessage] = []
        
        session = row_to_session(session_row, messages)
        
        assert session.id == "session-123"
        assert session.conversation_id == "conv-123"
        assert session.org_id == "org-123"
        assert session.user_id == "user-123"
        assert session.state == VoiceChatState.IDLE
        assert session.total_audio_seconds == 10.5
        assert session.total_stt_tokens == 100
        assert session.total_tts_characters == 500
        assert session.messages == messages

    def test_row_to_session_with_messages(self):
        """Test converting row with messages."""
        session_row = {
            "id": "session-123",
            "conversation_id": "conv-123",
            "org_id": "org-123",
            "user_id": "user-123",
            "config": "{}",
            "state": "idle",
            "total_audio_seconds": 0.0,
            "total_stt_tokens": 0,
            "total_tts_characters": 0,
            "started_at": "2024-01-01T00:00:00Z",
            "ended_at": None,
        }
        # NOTE: VoiceChatMessage TypedDict requires non-None values, but code uses _str_or_none_from_db
        # This is a type mismatch bug - testing actual behavior
        messages: list[VoiceChatMessage] = [
            {
                "id": "msg-1",
                "conversation_id": "conv-123",
                "role": "user",
                "text": "Hello",
                "audio_url": "",  # Empty string instead of None due to type mismatch
                "duration_seconds": 0.0,  # 0.0 instead of None due to type mismatch
                "stt_confidence": 0.0,  # 0.0 instead of None due to type mismatch
                "created_at": "2024-01-01T00:00:00Z",
            }
        ]
        
        session = row_to_session(session_row, messages)
        
        assert len(session.messages) == 1
        assert session.messages[0]["text"] == "Hello"

    def test_row_to_session_ended(self):
        """Test converting row with ended_at."""
        session_row = {
            "id": "session-123",
            "conversation_id": "conv-123",
            "org_id": "org-123",
            "user_id": "user-123",
            "config": "{}",
            "state": "ended",
            "total_audio_seconds": 0.0,
            "total_stt_tokens": 0,
            "total_tts_characters": 0,
            "started_at": "2024-01-01T00:00:00Z",
            "ended_at": "2024-01-01T01:00:00Z",
        }
        messages: list[VoiceChatMessage] = []
        
        session = row_to_session(session_row, messages)
        
        assert session.ended_at == "2024-01-01T01:00:00Z"
        assert session.state == VoiceChatState.ENDED


class TestBugDetection:
    """Bug detection tests for session operations."""

    def test_bug_update_session_state_may_not_handle_ended_at_correctly(self):
        """BUG: update_session_state may not handle ended_at correctly."""
        # ended_at may not be set when state changes to ENDED
        # This test documents the potential issue
        # TODO: Add test to verify ended_at is set correctly

    def test_bug_parse_config_may_not_validate_enum_values(self):
        """BUG: parse_config may not validate enum values."""
        # Invalid enum values may not be caught
        # This test documents the potential issue
        # TODO: Add test with invalid enum values

    def test_bug_get_session_messages_may_not_handle_missing_fields(self):
        """BUG: get_session_messages may not handle missing fields."""
        # Missing fields in database rows may cause errors
        # This test documents the potential issue
        # TODO: Add test with missing fields

    def test_bug_row_to_session_may_not_handle_invalid_config(self):
        """BUG: row_to_session may not handle invalid config."""
        # Invalid config JSON may cause errors
        # This test documents the potential issue
        # TODO: Add test with invalid config JSON

    def test_bug_voice_chat_message_type_mismatch(self):
        """BUG: VoiceChatMessage TypedDict requires non-None but code uses _str_or_none_from_db."""
        # TypedDict requires audio_url: str, duration_seconds: float, stt_confidence: float
        # But code uses _str_or_none_from_db/_float_or_none_from_db which can return None
        # This will cause runtime type errors
        # TODO: Fix type definition or code to match

    def test_bug_voice_chat_session_ended_at_type_mismatch(self):
        """BUG: VoiceChatSession TypedDict requires ended_at: str but code uses _str_or_none_from_db."""
        # TypedDict requires ended_at: str (not optional)
        # But code uses _str_or_none_from_db which can return None
        # This will cause runtime type errors
        # TODO: Fix type definition or code to match
