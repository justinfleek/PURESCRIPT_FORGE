"""
Voice Engine Database Schema - Table definitions and initialization.

This module contains SQL schema definitions for voice chat tables.
"""

from __future__ import annotations

from typing import TYPE_CHECKING


if TYPE_CHECKING:
    from .protocols import VoiceDatabaseProtocol


# =============================================================================
# Database Schema
# =============================================================================


VOICE_CHAT_SESSIONS_TABLE = """
CREATE TABLE IF NOT EXISTS voice_chat_sessions (
    id TEXT PRIMARY KEY,
    conversation_id TEXT NOT NULL,
    org_id TEXT NOT NULL,
    user_id TEXT NOT NULL,
    config TEXT NOT NULL,
    state TEXT NOT NULL CHECK (state IN ('idle', 'listening', 'processing',
                                      'thinking', 'speaking', 'interrupted', 'error')),
    total_audio_seconds REAL NOT NULL DEFAULT 0.0,
    total_stt_tokens INTEGER NOT NULL DEFAULT 0,
    total_tts_characters INTEGER NOT NULL DEFAULT 0,
    started_at TEXT NOT NULL,
    ended_at TEXT,
    FOREIGN KEY (conversation_id) REFERENCES conversations(id) ON DELETE CASCADE,
    FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE,
    FOREIGN KEY (org_id) REFERENCES organizations(id)
);
"""

VOICE_CHAT_MESSAGES_TABLE = """
CREATE TABLE IF NOT EXISTS voice_chat_messages (
    id TEXT PRIMARY KEY,
    session_id TEXT NOT NULL,
    conversation_id TEXT NOT NULL,
    role TEXT NOT NULL CHECK (role IN ('user', 'assistant')),
    text TEXT NOT NULL,
    audio_url TEXT,
    duration_seconds REAL,
    stt_confidence REAL,
    created_at TEXT NOT NULL,
    FOREIGN KEY (session_id) REFERENCES voice_chat_sessions(id) ON DELETE CASCADE,
    FOREIGN KEY (conversation_id) REFERENCES conversations(id) ON DELETE CASCADE
);
"""


# =============================================================================
# Initialization Functions
# =============================================================================


async def init_voice_tables(db: VoiceDatabaseProtocol) -> None:
    """Initialize voice engine tables."""
    await db.execute(VOICE_CHAT_SESSIONS_TABLE)
    await db.execute(VOICE_CHAT_MESSAGES_TABLE)


# =============================================================================
# Exports
# =============================================================================

__all__ = [
    "VOICE_CHAT_SESSIONS_TABLE",
    "VOICE_CHAT_MESSAGES_TABLE",
    "init_voice_tables",
]
