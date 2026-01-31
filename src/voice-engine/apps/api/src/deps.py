"""
FastAPI Dependencies - Full integration with Bridge Server.
"""

from toolbox.core import User
from toolbox.engines.voice_chat import VoiceChatEngine
from toolbox.engines.voice import VoiceEngine
from .services import VoiceServices

# Global services (initialized on startup)
_voice_services: VoiceServices | None = None


def get_current_user() -> User:
    """
    Get current authenticated user.
    
    TODO: Extract from JWT token or session when auth is implemented.
    For now, returns default user.
    """
    return User(id="default_user", email="user@example.com", org_id="default_org")


def get_voice_chat_engine_service() -> VoiceChatEngine:
    """Get voice chat engine service."""
    if _voice_services is None:
        raise RuntimeError("Voice services not initialized. Call init_voice_services() first.")
    return _voice_services.voice_chat_engine


def get_voice_engine_service() -> VoiceEngine:
    """Get voice engine service."""
    if _voice_services is None:
        raise RuntimeError("Voice services not initialized. Call init_voice_services() first.")
    return _voice_services.voice_engine


def get_database_service():
    """Get database service."""
    if _voice_services is None:
        raise RuntimeError("Voice services not initialized. Call init_voice_services() first.")
    return _voice_services.database


def init_voice_services(services: VoiceServices) -> None:
    """Initialize voice services."""
    global _voice_services
    _voice_services = services


# Exports for routes
_voice_engine = property(lambda self: get_voice_engine_service())
_database = property(lambda self: get_database_service())


__all__ = [
    "get_current_user",
    "get_voice_chat_engine_service",
    "get_voice_engine_service",
    "get_database_service",
    "init_voice_services",
    "VoiceServices",
]
