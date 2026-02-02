"""
Database Primitive Types - Minimal implementation for voice engine.
"""

from __future__ import annotations

from collections.abc import Sequence
from datetime import date, datetime
from typing import TypeVar

# SQLite/DuckDB accept these types as query parameters
DBParam = str | int | float | bool | None
"""A single query parameter value."""

DBParams = Sequence[DBParam]
"""Parameters for parameterized queries."""

# Result types
DBPrimitive = str | int | float | bool | bytes | datetime | date | None
"""A single database column value returned from queries."""

DatabaseRow = dict[str, DBPrimitive]
"""A row returned from fetch_one/fetch_all."""

__all__ = [
    "DBParam",
    "DBParams",
    "DBPrimitive",
    "DatabaseRow",
]
