"""
Core utilities.
"""

from dataclasses import dataclass
from typing import TypedDict


@dataclass(frozen=True)
class User:
    """User model for authentication."""
    id: str
    email: str
    org_id: str | None = None


__all__ = ["User"]
