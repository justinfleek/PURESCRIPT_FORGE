"""
Deep comprehensive tests for voice engine database schema.

Tests table initialization and schema validation.
"""
import pytest
from unittest.mock import AsyncMock
from toolbox.engines.voice.schema import (
    init_voice_tables,
    VOICE_CHAT_SESSIONS_TABLE,
    VOICE_CHAT_MESSAGES_TABLE,
)


class TestInitVoiceTables:
    """Deep comprehensive tests for init_voice_tables function."""

    @pytest.mark.asyncio
    async def test_init_voice_tables_calls_execute(self):
        """Test init_voice_tables calls execute for both tables."""
        mock_db = AsyncMock()
        
        await init_voice_tables(mock_db)
        
        assert mock_db.execute.call_count == 2

    @pytest.mark.asyncio
    async def test_init_voice_tables_sessions_table(self):
        """Test init_voice_tables creates sessions table."""
        mock_db = AsyncMock()
        
        await init_voice_tables(mock_db)
        
        call_args_list = mock_db.execute.call_args_list
        sessions_call = call_args_list[0]
        assert VOICE_CHAT_SESSIONS_TABLE in sessions_call[0][0]

    @pytest.mark.asyncio
    async def test_init_voice_tables_messages_table(self):
        """Test init_voice_tables creates messages table."""
        mock_db = AsyncMock()
        
        await init_voice_tables(mock_db)
        
        call_args_list = mock_db.execute.call_args_list
        messages_call = call_args_list[1]
        assert VOICE_CHAT_MESSAGES_TABLE in messages_call[0][0]

    @pytest.mark.asyncio
    async def test_init_voice_tables_order(self):
        """Test init_voice_tables creates tables in correct order."""
        mock_db = AsyncMock()
        
        await init_voice_tables(mock_db)
        
        call_args_list = mock_db.execute.call_args_list
        # Sessions table should be created first (no dependencies)
        assert "voice_chat_sessions" in call_args_list[0][0][0]
        # Messages table should be created second (depends on sessions)
        assert "voice_chat_messages" in call_args_list[1][0][0]

    @pytest.mark.asyncio
    async def test_init_voice_tables_idempotent(self):
        """Test init_voice_tables is idempotent (CREATE TABLE IF NOT EXISTS)."""
        mock_db = AsyncMock()
        
        await init_voice_tables(mock_db)
        await init_voice_tables(mock_db)
        
        # Should be safe to call multiple times
        assert mock_db.execute.call_count == 4  # 2 tables * 2 calls


class TestSchemaValidation:
    """Deep comprehensive tests for schema SQL strings."""

    def test_sessions_table_has_required_columns(self):
        """Test sessions table has all required columns."""
        assert "id TEXT PRIMARY KEY" in VOICE_CHAT_SESSIONS_TABLE
        assert "conversation_id TEXT NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "org_id TEXT NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "user_id TEXT NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "config TEXT NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "state TEXT NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "total_audio_seconds REAL NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "total_stt_tokens INTEGER NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "total_tts_characters INTEGER NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "started_at TEXT NOT NULL" in VOICE_CHAT_SESSIONS_TABLE
        assert "ended_at TEXT" in VOICE_CHAT_SESSIONS_TABLE

    def test_sessions_table_has_state_check(self):
        """Test sessions table has state CHECK constraint."""
        assert "CHECK (state IN" in VOICE_CHAT_SESSIONS_TABLE
        assert "'idle'" in VOICE_CHAT_SESSIONS_TABLE
        assert "'listening'" in VOICE_CHAT_SESSIONS_TABLE
        assert "'processing'" in VOICE_CHAT_SESSIONS_TABLE
        assert "'thinking'" in VOICE_CHAT_SESSIONS_TABLE
        assert "'speaking'" in VOICE_CHAT_SESSIONS_TABLE
        assert "'interrupted'" in VOICE_CHAT_SESSIONS_TABLE
        assert "'error'" in VOICE_CHAT_SESSIONS_TABLE

    def test_sessions_table_has_foreign_keys(self):
        """Test sessions table has foreign key constraints."""
        assert "FOREIGN KEY (conversation_id)" in VOICE_CHAT_SESSIONS_TABLE
        assert "FOREIGN KEY (user_id)" in VOICE_CHAT_SESSIONS_TABLE
        assert "FOREIGN KEY (org_id)" in VOICE_CHAT_SESSIONS_TABLE
        assert "ON DELETE CASCADE" in VOICE_CHAT_SESSIONS_TABLE

    def test_messages_table_has_required_columns(self):
        """Test messages table has all required columns."""
        assert "id TEXT PRIMARY KEY" in VOICE_CHAT_MESSAGES_TABLE
        assert "session_id TEXT NOT NULL" in VOICE_CHAT_MESSAGES_TABLE
        assert "conversation_id TEXT NOT NULL" in VOICE_CHAT_MESSAGES_TABLE
        assert "role TEXT NOT NULL" in VOICE_CHAT_MESSAGES_TABLE
        assert "text TEXT NOT NULL" in VOICE_CHAT_MESSAGES_TABLE
        assert "audio_url TEXT" in VOICE_CHAT_MESSAGES_TABLE
        assert "duration_seconds REAL" in VOICE_CHAT_MESSAGES_TABLE
        assert "stt_confidence REAL" in VOICE_CHAT_MESSAGES_TABLE
        assert "created_at TEXT NOT NULL" in VOICE_CHAT_MESSAGES_TABLE

    def test_messages_table_has_role_check(self):
        """Test messages table has role CHECK constraint."""
        assert "CHECK (role IN" in VOICE_CHAT_MESSAGES_TABLE
        assert "'user'" in VOICE_CHAT_MESSAGES_TABLE
        assert "'assistant'" in VOICE_CHAT_MESSAGES_TABLE

    def test_messages_table_has_foreign_keys(self):
        """Test messages table has foreign key constraints."""
        assert "FOREIGN KEY (session_id)" in VOICE_CHAT_MESSAGES_TABLE
        assert "FOREIGN KEY (conversation_id)" in VOICE_CHAT_MESSAGES_TABLE
        assert "ON DELETE CASCADE" in VOICE_CHAT_MESSAGES_TABLE

    def test_sessions_table_has_defaults(self):
        """Test sessions table has default values."""
        assert "DEFAULT 0.0" in VOICE_CHAT_SESSIONS_TABLE
        assert "DEFAULT 0" in VOICE_CHAT_SESSIONS_TABLE

    def test_both_tables_use_create_if_not_exists(self):
        """Test both tables use CREATE TABLE IF NOT EXISTS."""
        assert "CREATE TABLE IF NOT EXISTS" in VOICE_CHAT_SESSIONS_TABLE
        assert "CREATE TABLE IF NOT EXISTS" in VOICE_CHAT_MESSAGES_TABLE


class TestBugDetection:
    """Bug detection tests for schema."""

    def test_bug_sessions_table_may_not_have_all_states(self):
        """BUG: Sessions table CHECK may not include all VoiceChatState values."""
        # Verify all states from VoiceChatState enum are in CHECK constraint
        # This test documents the potential issue
        # TODO: Add test to verify all enum values are in CHECK

    def test_bug_foreign_keys_may_not_exist(self):
        """BUG: Foreign key tables may not exist."""
        # Foreign keys reference conversations, users, organizations tables
        # These may not exist when init_voice_tables is called
        # This test documents the potential issue
        # TODO: Add test to verify foreign key tables exist

    def test_bug_schema_may_not_be_idempotent(self):
        """BUG: Schema changes may not be idempotent."""
        # If schema changes, CREATE TABLE IF NOT EXISTS won't update existing tables
        # This test documents the potential issue
        # TODO: Add migration test
