"""
Voice Engine Session Operations - Database operations for voice chat sessions.

This module contains database operations for voice chat sessions and messages.
"""

from __future__ import annotations

import json
from typing import Literal

from .protocols import VoiceDatabaseProtocol
from .types import (
    DatabaseRow,
    DBPrimitive,
    VoiceChatConfig,
    VoiceChatMessage,
    VoiceChatMode,
    VoiceChatSession,
    VoiceChatState,
    VoiceQuality,
    _float_from_db,
    _float_or_none_from_db,
    _int_from_db,
    _str_from_db,
    _str_or_none_from_db,
)


# =============================================================================
# Session Database Operations
# =============================================================================


async def save_session(
    db: VoiceDatabaseProtocol,
    session_id: str,
    conversation_id: str,
    org_id: str,
    user_id: str,
    config: VoiceChatConfig,
    state: VoiceChatState,
    started_at: str,
) -> None:
    """Save session to database."""
    query = """
    INSERT INTO voice_chat_sessions (
        id, conversation_id, org_id, user_id, config, state,
        total_audio_seconds, total_stt_tokens, total_tts_characters,
        started_at, ended_at
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """

    await db.execute(
        query,
        (
            session_id,
            conversation_id,
            org_id,
            user_id,
            json.dumps(config),
            state.value,
            0.0,
            0,
            0,
            started_at,
            None,
        ),
    )


async def get_session_row(db: VoiceDatabaseProtocol, session_id: str) -> DatabaseRow | None:
    """Get session from database."""
    query = """
    SELECT id, conversation_id, org_id, user_id, config, state,
           total_audio_seconds, total_stt_tokens, total_tts_characters,
           started_at, ended_at
    FROM voice_chat_sessions
    WHERE id = ?
    """

    return await db.fetch_one(query, (session_id,))


async def update_session_state(
    db: VoiceDatabaseProtocol,
    session_id: str,
    state: VoiceChatState,
    ended_at: str | None = None,
) -> None:
    """Update session state."""
    query = "UPDATE voice_chat_sessions SET state = ?"
    params: tuple[DBPrimitive, ...] = (state.value,)

    if ended_at:
        query += ", ended_at = ?"
        params = (state.value, ended_at)

    query += " WHERE id = ?"
    params = params + (session_id,)

    await db.execute(query, params)


async def update_session_audio_seconds(
    db: VoiceDatabaseProtocol,
    session_id: str,
    duration: float,
) -> None:
    """Update total audio seconds for session."""
    query = """
    UPDATE voice_chat_sessions
    SET total_audio_seconds = total_audio_seconds + ?
    WHERE id = ?
    """

    await db.execute(query, (duration, session_id))


async def update_session_tts_characters(
    db: VoiceDatabaseProtocol,
    session_id: str,
    character_count: int,
) -> None:
    """Update total TTS characters for session."""
    query = """
    UPDATE voice_chat_sessions
    SET total_tts_characters = total_tts_characters + ?
    WHERE id = ?
    """

    await db.execute(query, (character_count, session_id))


# =============================================================================
# Message Database Operations
# =============================================================================


async def save_message(
    db: VoiceDatabaseProtocol,
    message_id: str,
    session_id: str,
    conversation_id: str,
    role: Literal["user", "assistant"],
    text: str,
    audio_url: str | None,
    duration_seconds: float | None,
    stt_confidence: float | None,
    created_at: str,
) -> None:
    """Save message to database."""
    query = """
    INSERT INTO voice_chat_messages (
        id, session_id, conversation_id, role, text, audio_url,
        duration_seconds, stt_confidence, created_at
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    """

    await db.execute(
        query,
        (
            message_id,
            session_id,
            conversation_id,
            role,
            text,
            audio_url,
            duration_seconds,
            stt_confidence,
            created_at,
        ),
    )


async def get_session_messages(
    db: VoiceDatabaseProtocol,
    session_id: str,
) -> list[VoiceChatMessage]:
    """Get all messages for a session."""
    query = """
    SELECT id, session_id, conversation_id, role, text, audio_url,
           duration_seconds, stt_confidence, created_at
    FROM voice_chat_messages
    WHERE session_id = ?
    ORDER BY created_at ASC
    """

    rows = await db.fetch_all(query, (session_id,))

    messages: list[VoiceChatMessage] = []
    for row in rows:
        raw_role = _str_from_db(row.get("role", "user"))
        role: Literal["user", "assistant"] = "assistant" if raw_role == "assistant" else "user"
        messages.append(
            VoiceChatMessage(
                id=_str_from_db(row.get("id", "")),
                conversation_id=_str_from_db(row.get("conversation_id", "")),
                role=role,
                text=_str_from_db(row.get("text", "")),
                audio_url=_str_or_none_from_db(row.get("audio_url")),
                duration_seconds=_float_or_none_from_db(row.get("duration_seconds")),
                stt_confidence=_float_or_none_from_db(row.get("stt_confidence")),
                created_at=_str_from_db(row.get("created_at", "")),
            )
        )

    return messages


# =============================================================================
# Config Parsing
# =============================================================================


def parse_config(config_json: str) -> VoiceChatConfig:
    """Parse config from JSON."""
    try:
        parsed: dict[str, str | float | int | bool] = json.loads(config_json)
        # Build config with proper type handling
        config = VoiceChatConfig()
        if "voice" in parsed and isinstance(parsed["voice"], str):
            config["voice"] = parsed["voice"]
        if "quality" in parsed and isinstance(parsed["quality"], str):
            config["quality"] = VoiceQuality(parsed["quality"])
        if "mode" in parsed and isinstance(parsed["mode"], str):
            config["mode"] = VoiceChatMode(parsed["mode"])
        if "language" in parsed and isinstance(parsed["language"], str):
            config["language"] = parsed["language"]
        if "speed" in parsed and isinstance(parsed["speed"], (int, float)):
            config["speed"] = float(parsed["speed"])
        if "vad_threshold" in parsed and isinstance(parsed["vad_threshold"], (int, float)):
            config["vad_threshold"] = float(parsed["vad_threshold"])
        if "silence_timeout_ms" in parsed and isinstance(parsed["silence_timeout_ms"], int):
            config["silence_timeout_ms"] = parsed["silence_timeout_ms"]
        if "max_duration_seconds" in parsed and isinstance(parsed["max_duration_seconds"], int):
            config["max_duration_seconds"] = parsed["max_duration_seconds"]
        if "interrupt_enabled" in parsed and isinstance(parsed["interrupt_enabled"], bool):
            config["interrupt_enabled"] = parsed["interrupt_enabled"]
        return config
    except (json.JSONDecodeError, TypeError, ValueError):
        return VoiceChatConfig()


def row_to_session(
    session_row: DatabaseRow,
    messages: list[VoiceChatMessage],
) -> VoiceChatSession:
    """Convert database row to VoiceChatSession."""
    return VoiceChatSession(
        id=_str_from_db(session_row.get("id", "")),
        conversation_id=_str_from_db(session_row.get("conversation_id", "")),
        org_id=_str_from_db(session_row.get("org_id", "")),
        user_id=_str_from_db(session_row.get("user_id", "")),
        config=parse_config(_str_from_db(session_row.get("config", "{}"))),
        state=VoiceChatState(_str_from_db(session_row.get("state", "idle"))),
        messages=messages,
        total_audio_seconds=_float_from_db(session_row.get("total_audio_seconds", 0.0)),
        total_stt_tokens=_int_from_db(session_row.get("total_stt_tokens", 0)),
        total_tts_characters=_int_from_db(session_row.get("total_tts_characters", 0)),
        started_at=_str_from_db(session_row.get("started_at", "")),
        ended_at=_str_or_none_from_db(session_row.get("ended_at")),
    )


# =============================================================================
# Exports
# =============================================================================

__all__ = [
    # Session operations
    "save_session",
    "get_session_row",
    "update_session_state",
    "update_session_audio_seconds",
    "update_session_tts_characters",
    # Message operations
    "save_message",
    "get_session_messages",
    # Config parsing
    "parse_config",
    "row_to_session",
]
