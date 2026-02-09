"""
SQLite Database Adapter - Implements VoiceDatabaseProtocol for voice engine.

Full integration with SQLite database used by Bridge Server.
"""

from __future__ import annotations

import aiosqlite
import logging
from pathlib import Path
from typing import Sequence

from .types import DBParams, DatabaseRow

logger = logging.getLogger(__name__)


class SQLiteVoiceDatabase:
    """
    SQLite database adapter implementing VoiceDatabaseProtocol.
    
    Uses aiosqlite for async SQLite operations.
    Compatible with Bridge Server database schema.
    """

    def __init__(self, db_path: str | Path) -> None:
        """
        Initialize SQLite database adapter.

        Args:
            db_path: Path to SQLite database file
        """
        self.db_path = Path(db_path)
        self._conn: aiosqlite.Connection | None = None

    async def connect(self) -> None:
        """Connect to database."""
        if self._conn is None:
            # Ensure parent directory exists
            self.db_path.parent.mkdir(parents=True, exist_ok=True)
            
            self._conn = await aiosqlite.connect(str(self.db_path))
            self._conn.row_factory = aiosqlite.Row
            
            # Enable foreign keys
            await self._conn.execute("PRAGMA foreign_keys = ON")
            await self._conn.commit()
            
            logger.info(f"Connected to SQLite database: {self.db_path}")

    async def close(self) -> None:
        """Close database connection."""
        if self._conn:
            await self._conn.close()
            self._conn = None
            logger.info("Closed SQLite database connection")

    async def execute(self, query: str, params: DBParams = ()) -> None:
        """
        Execute a query with no return value.

        Args:
            query: SQL query
            params: Query parameters
        """
        if self._conn is None:
            await self.connect()
        
        await self._conn.execute(query, params)
        await self._conn.commit()

    async def fetch_one(self, query: str, params: DBParams = ()) -> DatabaseRow | None:
        """
        Fetch a single row, or None if not found.

        Args:
            query: SQL query
            params: Query parameters

        Returns:
            Database row or None
        """
        if self._conn is None:
            await self.connect()
        
        cursor = await self._conn.execute(query, params)
        row = await cursor.fetchone()
        
        if row is None:
            return None
        
        # Convert Row to dict
        return dict(row)

    async def fetch_all(self, query: str, params: DBParams = ()) -> list[DatabaseRow]:
        """
        Fetch all matching rows.

        Args:
            query: SQL query
            params: Query parameters

        Returns:
            List of database rows
        """
        if self._conn is None:
            await self.connect()
        
        cursor = await self._conn.execute(query, params)
        rows = await cursor.fetchall()
        
        # Convert Rows to dicts
        return [dict(row) for row in rows]

    async def __aenter__(self):
        """Async context manager entry."""
        await self.connect()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        await self.close()


__all__ = ["SQLiteVoiceDatabase"]
