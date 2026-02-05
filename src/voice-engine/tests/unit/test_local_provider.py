"""
Deep comprehensive tests for Local Model TTS Provider.

Tests LocalModelTTSProvider, registry, utils, types, and bug detection.
"""
import pytest
from unittest.mock import AsyncMock, MagicMock, patch, mock_open
from pathlib import Path
import tempfile
import os
from toolbox.engines.voice_local_provider import (
    LocalModelTTSProvider,
    create_local_model_tts_provider,
    init_tts_models_table,
)
from toolbox.engines.voice_local_provider.registry import MODELS_REGISTRY
from toolbox.engines.voice_local_provider.utils import wav_to_mp3, calculate_model_sha
from toolbox.engines.voice_local_provider.types import (
    VoiceDatabaseProtocol,
    TTSModelInfo,
    MODELS_TABLE,
)


class MockDatabase:
    """Mock database for testing."""

    def __init__(self):
        self.queries = []
        self.rows = {}

    async def execute(self, query: str, params=()):
        """Mock execute."""
        self.queries.append((query, params))

    async def fetch_one(self, query: str, params=()):
        """Mock fetch_one."""
        key = str(params[0]) if params else None
        return self.rows.get(key)


class TestLocalModelTTSProvider:
    """Deep comprehensive tests for LocalModelTTSProvider."""

    @pytest.fixture
    def mock_db(self):
        """Create mock database."""
        return MockDatabase()

    @pytest.fixture
    def temp_models_dir(self):
        """Create temporary models directory."""
        with tempfile.TemporaryDirectory() as tmpdir:
            yield Path(tmpdir)

    @pytest.fixture
    def provider(self, mock_db, temp_models_dir):
        """Create LocalModelTTSProvider instance."""
        return LocalModelTTSProvider(
            db=mock_db,
            model_id="qwen3-tts-customvoice",
            models_dir=temp_models_dir,
            device="cpu",
        )

    def test_initialization_with_registry_model(self, mock_db, temp_models_dir):
        """Test initialization with model from registry."""
        provider = LocalModelTTSProvider(
            db=mock_db,
            model_id="qwen3-tts-customvoice",
            models_dir=temp_models_dir,
        )
        assert provider.model_id == "qwen3-tts-customvoice"
        assert provider._model_info["hf_repo"] == "Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice"
        assert provider._model is None
        assert provider._tokenizer is None

    def test_initialization_with_custom_model(self, mock_db, temp_models_dir):
        """Test initialization with custom model not in registry."""
        provider = LocalModelTTSProvider(
            db=mock_db,
            model_id="custom-model",
            hf_repo="Custom/Model",
            expected_sha="abc123",
            models_dir=temp_models_dir,
        )
        assert provider.model_id == "custom-model"
        assert provider._model_info["hf_repo"] == "Custom/Model"
        assert provider._model_info["expected_sha"] == "abc123"

    def test_initialization_creates_models_dir(self, mock_db):
        """Test initialization creates models directory."""
        with tempfile.TemporaryDirectory() as tmpdir:
            models_dir = Path(tmpdir) / "models" / "tts"
            provider = LocalModelTTSProvider(
                db=mock_db,
                model_id="qwen3-tts-customvoice",
                models_dir=models_dir,
            )
            assert models_dir.exists()

    def test_get_available_voices(self, provider: LocalModelTTSProvider):
        """Test get_available_voices returns Qwen speakers."""
        voices = provider.get_available_voices()
        assert len(voices) == 9
        assert "Ryan" in voices
        assert "Vivian" in voices
        assert "Sophia" in voices

    def test_estimate_cost_always_zero(self, provider: LocalModelTTSProvider):
        """Test estimate_cost always returns zero."""
        cost = provider.estimate_cost("any text")
        assert cost == 0.0

    @pytest.mark.asyncio
    async def test_synthesize_empty_text_raises_error(self, provider: LocalModelTTSProvider):
        """Test synthesize with empty text raises ValueError."""
        with pytest.raises(ValueError, match="Text cannot be empty"):
            await provider.synthesize("")

    @pytest.mark.asyncio
    async def test_synthesize_checks_cache_first(self, provider: LocalModelTTSProvider):
        """Test synthesize checks audio cache first."""
        mock_db = MockDatabase()
        mock_db.rows["qwen3-tts-customvoice"] = {
            "id": "qwen3-tts-customvoice",
            "status": "ready",
            "local_path": str(provider.models_dir / "qwen3-tts-customvoice"),
        }
        provider.db = mock_db

        # Mock model directory exists
        model_dir = provider.models_dir / "qwen3-tts-customvoice"
        model_dir.mkdir(parents=True, exist_ok=True)

        # Mock audio cache
        with patch("toolbox.engines.voice_local_provider.provider.get_audio_cache") as mock_cache:
            mock_cache_instance = MagicMock()
            mock_cache_instance.get.return_value = b"cached_audio"
            mock_cache.return_value = mock_cache_instance

            # Mock model loading
            with patch.object(provider, "_ensure_model_loaded"):
                result = await provider.synthesize("test text", "Ryan")
                assert result == b"cached_audio"
                mock_cache_instance.get.assert_called_once()

    @pytest.mark.asyncio
    async def test_synthesize_generates_audio(self, provider: LocalModelTTSProvider):
        """Test synthesize generates audio when not cached."""
        mock_db = MockDatabase()
        mock_db.rows["qwen3-tts-customvoice"] = {
            "id": "qwen3-tts-customvoice",
            "status": "ready",
            "local_path": str(provider.models_dir / "qwen3-tts-customvoice"),
        }
        provider.db = mock_db

        # Mock model directory exists
        model_dir = provider.models_dir / "qwen3-tts-customvoice"
        model_dir.mkdir(parents=True, exist_ok=True)

        # Mock audio cache miss
        with patch("toolbox.engines.voice_local_provider.provider.get_audio_cache") as mock_cache:
            mock_cache_instance = MagicMock()
            mock_cache_instance.get.return_value = None
            mock_cache.return_value = mock_cache_instance

            # Mock model
            mock_model = MagicMock()
            mock_model.generate_custom_voice.return_value = ([b"audio_data"], 16000)
            provider._model = mock_model

            # Mock soundfile
            with patch("soundfile.write") as mock_sf_write, \
                 patch("io.BytesIO") as mock_bytesio:
                mock_buffer = MagicMock()
                mock_buffer.getvalue.return_value = b"wav_bytes"
                mock_bytesio.return_value = mock_buffer

                # Mock wav_to_mp3
                with patch("toolbox.engines.voice_local_provider.provider.wav_to_mp3") as mock_wav_to_mp3:
                    mock_wav_to_mp3.return_value = b"mp3_bytes"

                    result = await provider.synthesize("test text", "Ryan", format="mp3")
                    assert result == b"mp3_bytes"
                    mock_cache_instance.put.assert_called_once()

    @pytest.mark.asyncio
    async def test_synthesize_model_not_loaded_loads_model(self, provider: LocalModelTTSProvider):
        """Test synthesize loads model if not loaded."""
        mock_db = MockDatabase()
        mock_db.rows["qwen3-tts-customvoice"] = {
            "id": "qwen3-tts-customvoice",
            "status": "ready",
            "local_path": str(provider.models_dir / "qwen3-tts-customvoice"),
        }
        provider.db = mock_db

        model_dir = provider.models_dir / "qwen3-tts-customvoice"
        model_dir.mkdir(parents=True, exist_ok=True)

        with patch("toolbox.engines.voice_local_provider.provider.get_audio_cache") as mock_cache:
            mock_cache_instance = MagicMock()
            mock_cache_instance.get.return_value = None
            mock_cache.return_value = mock_cache_instance

            with patch.object(provider, "_ensure_model_loaded") as mock_load:
                mock_model = MagicMock()
                mock_model.generate_custom_voice.return_value = ([b"audio_data"], 16000)
                provider._model = mock_model

                with patch("soundfile.write"), \
                     patch("io.BytesIO") as mock_bytesio, \
                     patch("toolbox.engines.voice_local_provider.provider.wav_to_mp3") as mock_wav_to_mp3:
                    mock_buffer = MagicMock()
                    mock_buffer.getvalue.return_value = b"wav_bytes"
                    mock_bytesio.return_value = mock_buffer
                    mock_wav_to_mp3.return_value = b"mp3_bytes"

                    await provider.synthesize("test text")
                    mock_load.assert_called_once()

    @pytest.mark.asyncio
    async def test_ensure_model_downloaded_already_ready(self, provider: LocalModelTTSProvider):
        """Test ensure_model_downloaded returns True if model already ready."""
        mock_db = MockDatabase()
        model_dir = provider.models_dir / "qwen3-tts-customvoice"
        model_dir.mkdir(parents=True, exist_ok=True)
        mock_db.rows["qwen3-tts-customvoice"] = {
            "id": "qwen3-tts-customvoice",
            "status": "ready",
            "local_path": str(model_dir),
        }
        provider.db = mock_db

        result = await provider.ensure_model_downloaded()
        assert result is True

    @pytest.mark.asyncio
    async def test_ensure_model_downloaded_sha_mismatch(self, provider: LocalModelTTSProvider):
        """Test ensure_model_downloaded re-downloads on SHA mismatch."""
        mock_db = MockDatabase()
        mock_db.rows["qwen3-tts-customvoice"] = {
            "id": "qwen3-tts-customvoice",
            "status": "mismatch",
        }
        provider.db = mock_db

        with patch.object(provider, "_download_model") as mock_download:
            result = await provider.ensure_model_downloaded()
            assert result is False
            mock_download.assert_called_once()

    @pytest.mark.asyncio
    async def test_ensure_model_downloaded_downloads_if_not_exists(self, provider: LocalModelTTSProvider):
        """Test ensure_model_downloaded downloads if model not in database."""
        mock_db = MockDatabase()
        mock_db.rows["qwen3-tts-customvoice"] = None
        provider.db = mock_db

        with patch.object(provider, "_download_model") as mock_download:
            result = await provider.ensure_model_downloaded()
            assert result is True
            mock_download.assert_called_once()

    @pytest.mark.asyncio
    async def test_download_model(self, provider: LocalModelTTSProvider):
        """Test _download_model downloads and verifies model."""
        mock_db = MockDatabase()
        provider.db = mock_db

        model_dir = provider.models_dir / "qwen3-tts-customvoice"
        model_dir.mkdir(parents=True, exist_ok=True)

        with patch("huggingface_hub.snapshot_download") as mock_download, \
             patch("toolbox.engines.voice_local_provider.provider.calculate_model_sha") as mock_sha:
            mock_sha.return_value = "expected_sha"
            provider._model_info["expected_sha"] = "expected_sha"

            await provider._download_model()

            mock_download.assert_called_once()
            assert len(mock_db.queries) > 0

    @pytest.mark.asyncio
    async def test_download_model_sha_mismatch_raises_error(self, provider: LocalModelTTSProvider):
        """Test _download_model raises error on SHA mismatch."""
        mock_db = MockDatabase()
        provider.db = mock_db

        model_dir = provider.models_dir / "qwen3-tts-customvoice"
        model_dir.mkdir(parents=True, exist_ok=True)

        with patch("huggingface_hub.snapshot_download"), \
             patch("toolbox.engines.voice_local_provider.provider.calculate_model_sha") as mock_sha:
            mock_sha.return_value = "actual_sha"
            provider._model_info["expected_sha"] = "expected_sha"

            with pytest.raises(RuntimeError, match="SHA verification failed"):
                await provider._download_model()

    @pytest.mark.asyncio
    async def test_download_model_handles_import_error(self, provider: LocalModelTTSProvider):
        """Test _download_model handles ImportError."""
        mock_db = MockDatabase()
        provider.db = mock_db

        with patch("builtins.__import__", side_effect=ImportError("No module named huggingface_hub")):
            with pytest.raises(RuntimeError, match="huggingface_hub not installed"):
                await provider._download_model()

    @pytest.mark.asyncio
    async def test_ensure_model_loaded_loads_model(self, provider: LocalModelTTSProvider):
        """Test _ensure_model_loaded loads model."""
        mock_db = MockDatabase()
        model_dir = provider.models_dir / "qwen3-tts-customvoice"
        model_dir.mkdir(parents=True, exist_ok=True)
        mock_db.rows["qwen3-tts-customvoice"] = {
            "id": "qwen3-tts-customvoice",
            "status": "ready",
            "local_path": str(model_dir),
        }
        provider.db = mock_db

        with patch.object(provider, "ensure_model_downloaded"), \
             patch("torch"), \
             patch("sys.path"), \
             patch("qwen_tts.Qwen3TTSModel.from_pretrained") as mock_load:
            mock_model = MagicMock()
            mock_load.return_value = mock_model

            await provider._ensure_model_loaded()

            assert provider._model == mock_model

    @pytest.mark.asyncio
    async def test_ensure_model_loaded_model_not_found_raises_error(self, provider: LocalModelTTSProvider):
        """Test _ensure_model_loaded raises error if model record not found."""
        mock_db = MockDatabase()
        mock_db.rows["qwen3-tts-customvoice"] = None
        provider.db = mock_db

        with patch.object(provider, "ensure_model_downloaded"):
            with pytest.raises(RuntimeError, match="Model record not found"):
                await provider._ensure_model_loaded()

    @pytest.mark.asyncio
    async def test_get_model_record(self, provider: LocalModelTTSProvider):
        """Test _get_model_record fetches from database."""
        mock_db = MockDatabase()
        mock_db.rows["qwen3-tts-customvoice"] = {"id": "qwen3-tts-customvoice", "status": "ready"}
        provider.db = mock_db

        result = await provider._get_model_record()
        assert result == {"id": "qwen3-tts-customvoice", "status": "ready"}

    @pytest.mark.asyncio
    async def test_update_model_status(self, provider: LocalModelTTSProvider):
        """Test _update_model_status updates database."""
        mock_db = MockDatabase()
        provider.db = mock_db

        await provider._update_model_status("downloading", actual_sha="abc123", error_message="test")

        assert len(mock_db.queries) > 0
        query, params = mock_db.queries[-1]
        assert "downloading" in query or "downloading" in str(params)


class TestCreateLocalModelTTSProvider:
    """Deep comprehensive tests for create_local_model_tts_provider factory."""

    def test_create_provider(self):
        """Test factory creates provider."""
        mock_db = MockDatabase()
        with tempfile.TemporaryDirectory() as tmpdir:
            provider = create_local_model_tts_provider(
                db=mock_db,
                model_id="qwen3-tts-customvoice",
                models_dir=tmpdir,
            )
            assert isinstance(provider, LocalModelTTSProvider)
            assert provider.model_id == "qwen3-tts-customvoice"

    def test_create_provider_with_overrides(self):
        """Test factory creates provider with overrides."""
        mock_db = MockDatabase()
        with tempfile.TemporaryDirectory() as tmpdir:
            provider = create_local_model_tts_provider(
                db=mock_db,
                model_id="qwen3-tts-customvoice",
                hf_repo="Custom/Repo",
                expected_sha="custom_sha",
                models_dir=tmpdir,
                device="cuda:1",
            )
            assert provider._model_info["hf_repo"] == "Custom/Repo"
            assert provider.device == "cuda:1"


class TestModelsRegistry:
    """Deep comprehensive tests for MODELS_REGISTRY."""

    def test_registry_contains_expected_models(self):
        """Test registry contains expected models."""
        assert "qwen3-tts-customvoice" in MODELS_REGISTRY
        assert "qwen3-tts-voicedesign" in MODELS_REGISTRY
        assert "qwen3-tts-base" in MODELS_REGISTRY

    def test_registry_model_structure(self):
        """Test registry models have correct structure."""
        for model_id, model_info in MODELS_REGISTRY.items():
            assert "model_id" in model_info
            assert "hf_repo" in model_info
            assert "model_name" in model_info
            assert "expected_sha" in model_info
            assert "requires_gpu" in model_info
            assert "estimated_size_mb" in model_info

    def test_registry_model_ids_match_keys(self):
        """Test registry model IDs match dictionary keys."""
        for model_id, model_info in MODELS_REGISTRY.items():
            assert model_info["model_id"] == model_id


class TestUtils:
    """Deep comprehensive tests for utility functions."""

    def test_wav_to_mp3_converts(self):
        """Test wav_to_mp3 converts WAV to MP3."""
        # Mock WAV bytes (minimal WAV header)
        wav_bytes = b"RIFF\x24\x00\x00\x00WAVEfmt \x10\x00\x00\x00\x01\x00\x02\x00\x44\xac\x00\x00\x10\xb1\x02\x00\x04\x00\x10\x00data\x00\x00\x00\x00"

        with patch("pydub.AudioSegment.from_file") as mock_load:
            mock_audio = MagicMock()
            mock_buffer = MagicMock()
            mock_buffer.getvalue.return_value = b"mp3_bytes"
            mock_audio.export.return_value = None
            mock_load.return_value = mock_audio

            with patch("io.BytesIO") as mock_bytesio:
                mock_bytesio.return_value = mock_buffer
                result = wav_to_mp3(wav_bytes)
                assert result == b"mp3_bytes"

    def test_wav_to_mp3_returns_wav_on_import_error(self):
        """Test wav_to_mp3 returns WAV if pydub not installed."""
        wav_bytes = b"wav_data"
        with patch("builtins.__import__", side_effect=ImportError("No module named pydub")):
            result = wav_to_mp3(wav_bytes)
            assert result == wav_bytes

    def test_wav_to_mp3_returns_wav_on_conversion_error(self):
        """Test wav_to_mp3 returns WAV on conversion error."""
        wav_bytes = b"wav_data"
        with patch("pydub.AudioSegment.from_file", side_effect=Exception("Conversion failed")):
            result = wav_to_mp3(wav_bytes)
            assert result == wav_bytes

    @pytest.mark.asyncio
    async def test_calculate_model_sha(self):
        """Test calculate_model_sha calculates SHA256."""
        with tempfile.TemporaryDirectory() as tmpdir:
            model_dir = Path(tmpdir)
            (model_dir / "file1.txt").write_text("content1")
            (model_dir / "file2.txt").write_text("content2")

            sha = await calculate_model_sha(model_dir)
            assert isinstance(sha, str)
            assert len(sha) == 64  # SHA256 hex digest length

    @pytest.mark.asyncio
    async def test_calculate_model_sha_empty_directory(self):
        """Test calculate_model_sha handles empty directory."""
        with tempfile.TemporaryDirectory() as tmpdir:
            model_dir = Path(tmpdir)
            sha = await calculate_model_sha(model_dir)
            assert isinstance(sha, str)
            assert len(sha) == 64

    @pytest.mark.asyncio
    async def test_calculate_model_sha_ignores_directories(self):
        """Test calculate_model_sha ignores directories."""
        with tempfile.TemporaryDirectory() as tmpdir:
            model_dir = Path(tmpdir)
            (model_dir / "file.txt").write_text("content")
            (model_dir / "subdir").mkdir()
            (model_dir / "subdir" / "nested.txt").write_text("nested")

            sha = await calculate_model_sha(model_dir)
            assert isinstance(sha, str)


class TestInitTTSModelsTable:
    """Deep comprehensive tests for init_tts_models_table."""

    @pytest.mark.asyncio
    async def test_init_tts_models_table(self):
        """Test init_tts_models_table executes MODELS_TABLE."""
        mock_db = MockDatabase()
        await init_tts_models_table(mock_db)
        assert len(mock_db.queries) == 1
        assert "CREATE TABLE" in mock_db.queries[0][0].upper()


class TestBugDetection:
    """Bug detection tests for local provider."""

    @pytest.mark.asyncio
    async def test_bug_model_may_not_be_unloaded(self):
        """BUG: Model may not be unloaded correctly."""
        # Model may stay in memory after provider is destroyed
        # This test documents the potential issue
        # TODO: Add test to verify model unloading

    @pytest.mark.asyncio
    async def test_bug_sha_calculation_may_be_slow(self):
        """BUG: SHA calculation may be slow for large models."""
        # SHA calculation may block for large models
        # This test documents the potential issue
        # TODO: Add test with large model directory

    @pytest.mark.asyncio
    async def test_bug_concurrent_downloads_may_conflict(self):
        """BUG: Concurrent downloads may conflict."""
        # Multiple providers downloading same model may conflict
        # This test documents the potential issue
        # TODO: Add test with concurrent downloads

    @pytest.mark.asyncio
    async def test_bug_cache_may_not_be_cleared(self):
        """BUG: Audio cache may not be cleared correctly."""
        # Cache may accumulate entries without cleanup
        # This test documents the potential issue
        # TODO: Add test to verify cache cleanup
