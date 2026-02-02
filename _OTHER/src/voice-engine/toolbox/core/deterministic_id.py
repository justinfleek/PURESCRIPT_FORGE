"""
Deterministic ID Generation - Minimal implementation for voice engine.
"""

import hashlib
import hmac
import os
import uuid

FORGE_NAMESPACE = uuid.UUID("6ba7b810-9dad-11d1-80b4-00c04fd430c8")


def _get_secret() -> bytes:
    """Get the ID generation secret from environment or use default."""
    return os.environ.get("FORGE_ID_SECRET", "forge-default-id-secret").encode()


def make_uuid(*content: str) -> str:
    """Generate a deterministic UUID from content strings (UUID5 format)."""
    content_str = "|".join(content)
    return str(uuid.uuid5(FORGE_NAMESPACE, content_str))


__all__ = ["make_uuid"]
