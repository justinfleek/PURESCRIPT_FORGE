"""
Identity System - Minimal implementation for voice engine.
"""

from enum import Enum
from typing import Final
from uuid import UUID, uuid5

NAMESPACE_DNS: Final[UUID] = UUID("6ba7b810-9dad-11d1-80b4-00c04fd430c8")
NAMESPACE_FORGE: Final[UUID] = uuid5(NAMESPACE_DNS, "forge.ai")


class Namespace(Enum):
    """Entity namespaces."""
    ASSET = uuid5(NAMESPACE_FORGE, "asset")


def generate_id(namespace: Namespace, *parts: str) -> UUID:
    """Generate deterministic ID from namespace and parts."""
    content = "|".join(parts)
    return uuid5(namespace.value, content)

__all__ = ["Namespace", "generate_id"]
