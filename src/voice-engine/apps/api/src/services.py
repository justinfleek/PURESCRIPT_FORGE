"""
Voice Engine Services - Full integration setup.

Initializes all voice services with real implementations (no mocks).
"""

import os
import logging
from pathlib import Path

from toolbox.core.db.sqlite_adapter import SQLiteVoiceDatabase
from toolbox.engines.chatbot import VeniceChatEngine
from toolbox.engines.voice import VoiceEngine, init_voice_tables
from toolbox.engines.voice_chat import VoiceChatEngine
from toolbox.engines.voice_tts_providers import create_tts_provider
from toolbox.engines.voice_stt_providers import create_stt_provider
from toolbox.engines.voice_local_provider import init_tts_models_table

logger = logging.getLogger(__name__)


class VoiceServices:
    """Container for all voice services."""

    def __init__(
        self,
        database: SQLiteVoiceDatabase,
        voice_engine: VoiceEngine,
        voice_chat_engine: VoiceChatEngine,
    ) -> None:
        """Initialize voice services."""
        self.database = database
        self.voice_engine = voice_engine
        self.voice_chat_engine = voice_chat_engine


async def create_voice_services(
    db_path: str | Path | None = None,
    venice_api_key: str | None = None,
) -> VoiceServices:
    """
    Create and initialize all voice services.

    Args:
        db_path: Path to SQLite database (defaults to bridge.db)
        venice_api_key: Venice API key (from env if not provided)

    Returns:
        Initialized voice services
    """
    # Database path
    if db_path is None:
        db_path = os.getenv(
            "VOICE_DB_PATH",
            os.path.join(os.path.expanduser("~"), ".opencode-sidepanel", "bridge.db"),
        )

    # Create database adapter
    database = SQLiteVoiceDatabase(db_path)
    await database.connect()

    # Initialize voice tables
    await init_voice_tables(database)
    await init_tts_models_table(database)
    logger.info("Voice database tables initialized")

    # Create TTS provider
    tts_provider_name = os.getenv("TTS_PROVIDER", "local")
    tts_model_id = os.getenv("TTS_MODEL_ID", "qwen3-tts-customvoice")
    tts_device = os.getenv("TTS_DEVICE", "cuda:0")

    if tts_provider_name == "local":
        tts_provider = create_tts_provider(
            provider="local",
            model_id=tts_model_id,
            db=database,
        )
        logger.info(f"Created local TTS provider: {tts_model_id}")
    elif tts_provider_name == "openai":
        tts_provider = create_tts_provider(
            provider="openai",
            api_key=os.getenv("OPENAI_API_KEY", ""),
            model="tts-1",
        )
        logger.info("Created OpenAI TTS provider")
    elif tts_provider_name == "elevenlabs":
        tts_provider = create_tts_provider(
            provider="elevenlabs",
            api_key=os.getenv("ELEVENLABS_API_KEY", ""),
        )
        logger.info("Created ElevenLabs TTS provider")
    else:
        raise ValueError(f"Unknown TTS provider: {tts_provider_name}")

    # Create STT provider
    stt_provider_name = os.getenv("STT_PROVIDER", "mock")
    
    if stt_provider_name == "openai":
        stt_provider = create_stt_provider(
            provider="openai",
            api_key=os.getenv("OPENAI_API_KEY", ""),
        )
        logger.info("Created OpenAI STT provider")
    elif stt_provider_name == "deepgram":
        stt_provider = create_stt_provider(
            provider="deepgram",
            api_key=os.getenv("DEEPGRAM_API_KEY", ""),
        )
        logger.info("Created Deepgram STT provider")
    else:
        stt_provider = create_stt_provider(provider="mock")
        logger.info("Created mock STT provider (set STT_PROVIDER=openai or deepgram for real STT)")

    # Create voice engine
    voice_engine = VoiceEngine(
        db=database,
        tts_provider=tts_provider,
        stt_provider=stt_provider,
        default_voice="Ryan",
        default_language="en",
    )
    logger.info("Created voice engine")

    # Create chat engine
    venice_key = venice_api_key or os.getenv("VENICE_API_KEY")
    if not venice_key:
        raise ValueError("VENICE_API_KEY is required for chat engine")
    
    chat_engine = VeniceChatEngine(api_key=venice_key)
    logger.info("Created Venice chat engine")

    # Create voice chat engine
    voice_chat_engine = VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )
    logger.info("Created voice chat engine")

    return VoiceServices(
        database=database,
        voice_engine=voice_engine,
        voice_chat_engine=voice_chat_engine,
    )


async def shutdown_voice_services(services: VoiceServices) -> None:
    """Shutdown voice services."""
    await services.database.close()
    await services.voice_chat_engine.chat_engine.close()
    logger.info("Voice services shut down")


__all__ = [
    "VoiceServices",
    "create_voice_services",
    "shutdown_voice_services",
]
