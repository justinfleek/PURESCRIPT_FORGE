"""
Type definitions and database schema for Local Model TTS Provider.

Contains:
- VoiceDatabaseProtocol: Database interface
- TTSModelInfo: TypedDict for model metadata
- MODELS_TABLE: SQL schema for model tracking
"""

from __future__ import annotations

from typing import Protocol

from typing_extensions import TypedDict

from toolbox.core.db.types import DatabaseRow, DBParams


class VoiceDatabaseProtocol(Protocol):
    """Protocol for database connection used by TTS providers.

    Compatible with DatabaseConnection from toolbox.core.db.
    Uses DBParams (Sequence[DBPrimitive]) for parameters.
    """

    async def execute(self, query: str, params: DBParams = ()) -> None:
        """Execute a SQL query."""
        ...

    async def fetch_one(self, query: str, params: DBParams = ()) -> DatabaseRow | None:
        """Fetch a single row from the database."""
        ...


class TTSModelInfo(TypedDict):
    """Information about a TTS model from HuggingFace."""

    model_id: str  # Internal ID
    hf_repo: str  # HuggingFace repo path
    model_name: str  # Human-readable name
    expected_sha: str  # SHA256 of model files
    requires_gpu: bool
    estimated_size_mb: int


# =============================================================================
# Database Schema for Model Management
# =============================================================================

MODELS_TABLE = """
CREATE TABLE IF NOT EXISTS tts_models (
    id TEXT PRIMARY KEY,
    hf_repo TEXT NOT NULL UNIQUE,
    model_name TEXT NOT NULL,
    expected_sha TEXT NOT NULL,
    actual_sha TEXT,
    local_path TEXT,
    status TEXT NOT NULL CHECK (status IN ('downloading', 'ready', 'error', 'mismatch')),
    file_size_bytes INTEGER,
    download_date TEXT,
    last_verified_date TEXT,
    error_message TEXT,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
"""


__all__ = [
    "VoiceDatabaseProtocol",
    "TTSModelInfo",
    "MODELS_TABLE",
]
