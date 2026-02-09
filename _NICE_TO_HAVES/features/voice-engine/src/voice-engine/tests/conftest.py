"""
Pytest Configuration and Fixtures

Provides:
- Reproducible test distributions
- Common fixtures
- Test data generators
- Mock services
"""

import asyncio
import os
import tempfile
from pathlib import Path
from typing import AsyncGenerator, Generator

import pytest

from toolbox.core.db.sqlite_adapter import SQLiteVoiceDatabase
from toolbox.engines.voice_tts_providers import MockTTSProvider
from toolbox.engines.voice_stt_providers import MockSTTProvider
from toolbox.engines.voice import VoiceEngine


@pytest.fixture(scope="session")
def event_loop():
    """Create event loop for async tests."""
    loop = asyncio.get_event_loop_policy().new_event_loop()
    yield loop
    loop.close()


@pytest.fixture
async def test_db() -> AsyncGenerator[SQLiteVoiceDatabase, None]:
    """Create temporary test database."""
    with tempfile.NamedTemporaryFile(suffix=".db", delete=False) as f:
        db_path = f.name
    
    db = SQLiteVoiceDatabase(db_path)
    await db.connect()
    
    # Initialize tables
    from toolbox.engines.voice.schema import init_voice_tables
    from toolbox.engines.voice_local_provider import init_tts_models_table
    
    await init_voice_tables(db)
    await init_tts_models_table(db)
    
    yield db
    
    await db.close()
    os.unlink(db_path)


@pytest.fixture
def mock_tts_provider() -> MockTTSProvider:
    """Create mock TTS provider for testing."""
    return MockTTSProvider(default_voice="test_voice")


@pytest.fixture
def mock_stt_provider() -> MockSTTProvider:
    """Create mock STT provider for testing."""
    return MockSTTProvider(mock_transcript="test transcript")


@pytest.fixture
async def voice_engine(test_db: SQLiteVoiceDatabase, mock_tts_provider: MockTTSProvider, mock_stt_provider: MockSTTProvider) -> VoiceEngine:
    """Create voice engine with test providers."""
    return VoiceEngine(
        db=test_db,
        tts_provider=mock_tts_provider,
        stt_provider=mock_stt_provider,
        default_voice="test_voice",
        default_language="en",
    )


@pytest.fixture
def sample_audio_bytes() -> bytes:
    """Generate sample audio bytes for testing."""
    # Mock WAV header + minimal audio data
    return b"RIFF\x24\x00\x00\x00WAVEfmt \x10\x00\x00\x00\x01\x00\x01\x00\x44\xac\x00\x00\x88\x58\x01\x00\x02\x00\x10\x00data\x00\x00\x00\x00"


@pytest.fixture
def reproducible_seed() -> int:
    """Get reproducible random seed for tests."""
    return 42


__all__ = []
