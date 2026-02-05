"""
Deep comprehensive tests for STT providers (API clients).

Tests OpenAI Whisper, Deepgram, Mock providers, factory function, and bug detection.
"""
import pytest
from unittest.mock import AsyncMock, MagicMock, patch
from toolbox.engines.voice_stt_providers import (
    OpenAIWhisperProvider,
    DeepgramSTTProvider,
    MockSTTProvider,
    create_stt_provider,
)


class TestOpenAIWhisperProvider:
    """Deep comprehensive tests for OpenAIWhisperProvider."""

    @pytest.fixture
    def provider(self):
        """Create OpenAI Whisper provider instance."""
        return OpenAIWhisperProvider(
            api_key="test_key",
            model="whisper-1",
        )

    @pytest.mark.asyncio
    async def test_transcribe_basic(self, provider: OpenAIWhisperProvider):
        """Test basic transcription."""
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "text": "Hello, world!",
            "language": "en",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.transcribe(b"audio_data", "mp3")
        assert result["text"] == "Hello, world!"
        assert result["language"] == "en"
        assert result["confidence"] == 0.95
        assert isinstance(result["duration_seconds"], float)
        assert isinstance(result["cost_usd"], float)

    @pytest.mark.asyncio
    async def test_transcribe_invalid_model_raises_error(self):
        """Test invalid model raises ValueError."""
        provider = OpenAIWhisperProvider(api_key="test_key", model="invalid_model")
        with pytest.raises(ValueError, match="Invalid model"):
            await provider.transcribe(b"audio", "mp3")

    @pytest.mark.asyncio
    async def test_transcribe_invalid_format_raises_error(self, provider: OpenAIWhisperProvider):
        """Test invalid format raises ValueError."""
        with pytest.raises(ValueError, match="Unsupported audio format"):
            await provider.transcribe(b"audio", "invalid_format")  # type: ignore

    @pytest.mark.asyncio
    async def test_transcribe_all_valid_formats(self, provider: OpenAIWhisperProvider):
        """Test all valid formats."""
        mock_response = MagicMock()
        mock_response.json.return_value = {"text": "test", "language": "en"}
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        formats = ["mp3", "wav", "ogg", "flac", "webm", "m4a"]
        for fmt in formats:
            result = await provider.transcribe(b"audio", fmt)
            assert result["text"] == "test"

    @pytest.mark.asyncio
    async def test_transcribe_with_language(self, provider: OpenAIWhisperProvider):
        """Test transcription with specific language."""
        mock_response = MagicMock()
        mock_response.json.return_value = {"text": "Hola", "language": "es"}
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.transcribe(b"audio", "mp3", language="es")
        assert result["language"] == "es"
        
        # Check that language was passed to API
        call_args = mock_client.post.call_args
        assert call_args[1]["files"]["language"][1] == "es"

    @pytest.mark.asyncio
    async def test_transcribe_auto_language(self, provider: OpenAIWhisperProvider):
        """Test transcription with auto language detection."""
        mock_response = MagicMock()
        mock_response.json.return_value = {"text": "test", "language": "en"}
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.transcribe(b"audio", "mp3", language="auto")
        
        # Check that language was not passed to API (auto-detect)
        call_args = mock_client.post.call_args
        assert "language" not in call_args[1]["files"]

    @pytest.mark.asyncio
    async def test_transcribe_with_timestamps(self, provider: OpenAIWhisperProvider):
        """Test transcription with timestamps."""
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "text": "Hello world",
            "language": "en",
            "words": [
                {"word": "Hello", "start": 0.0, "end": 0.5},
                {"word": "world", "start": 0.5, "end": 1.0},
            ],
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.transcribe(b"audio", "mp3", include_timestamps=True)
        assert result["words"] is not None
        assert len(result["words"]) == 2

    @pytest.mark.asyncio
    async def test_transcribe_without_timestamps(self, provider: OpenAIWhisperProvider):
        """Test transcription without timestamps."""
        mock_response = MagicMock()
        mock_response.json.return_value = {"text": "test", "language": "en"}
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.transcribe(b"audio", "mp3", include_timestamps=False)
        assert result["words"] is None

    @pytest.mark.asyncio
    async def test_transcribe_http_error_raises_runtime_error(self, provider: OpenAIWhisperProvider):
        """Test HTTP error raises RuntimeError."""
        mock_response = MagicMock()
        mock_response.raise_for_status = MagicMock(side_effect=Exception("HTTP 500"))
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        with pytest.raises(RuntimeError, match="Transcription failed"):
            await provider.transcribe(b"audio", "mp3")

    def test_estimate_cost(self, provider: OpenAIWhisperProvider):
        """Test cost estimation."""
        cost = provider.estimate_cost(60.0)  # 1 minute
        assert cost > 0
        assert isinstance(cost, float)

    def test_estimate_cost_zero_duration(self, provider: OpenAIWhisperProvider):
        """Test cost estimation for zero duration."""
        cost = provider.estimate_cost(0.0)
        assert cost == 0.0

    def test_custom_base_url(self):
        """Test custom base URL."""
        provider = OpenAIWhisperProvider(
            api_key="test_key",
            base_url="https://custom.example.com/v1",
        )
        assert provider.base_url == "https://custom.example.com/v1"

    @pytest.mark.asyncio
    async def test_lazy_client_loading(self, provider: OpenAIWhisperProvider):
        """Test client is lazily loaded."""
        assert provider._client is None
        with patch("httpx.AsyncClient") as mock_client_class:
            mock_client = AsyncMock()
            mock_client_class.return_value = mock_client
            client = provider._get_client()
            assert client is not None
            mock_client_class.assert_called_once()

    @pytest.mark.asyncio
    async def test_bug_duration_estimation_may_not_be_accurate(self, provider: OpenAIWhisperProvider):
        """BUG: Duration estimation may not be accurate."""
        # Duration is estimated from word count, may not match actual audio
        # This test documents the potential issue
        # TODO: Add test to verify duration accuracy


class TestDeepgramSTTProvider:
    """Deep comprehensive tests for DeepgramSTTProvider."""

    @pytest.fixture
    def provider(self):
        """Create Deepgram STT provider instance."""
        return DeepgramSTTProvider(
            api_key="test_key",
            model="nova-2",
        )

    @pytest.mark.asyncio
    async def test_transcribe_basic(self, provider: DeepgramSTTProvider):
        """Test basic transcription."""
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "results": {
                "channels": [
                    {
                        "alternatives": [
                            {
                                "transcript": "Hello, world!",
                                "confidence": 0.95,
                            }
                        ]
                    }
                ],
                "metadata": {
                    "duration": 1.5,
                },
            }
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.transcribe(b"audio_data", "mp3")
        assert result["text"] == "Hello, world!"
        assert result["confidence"] == 0.95
        assert result["duration_seconds"] == 1.5

    @pytest.mark.asyncio
    async def test_transcribe_invalid_format_raises_error(self, provider: DeepgramSTTProvider):
        """Test invalid format raises ValueError."""
        with pytest.raises(ValueError, match="Unsupported audio format"):
            await provider.transcribe(b"audio", "invalid_format")  # type: ignore

    @pytest.mark.asyncio
    async def test_transcribe_all_valid_formats(self, provider: DeepgramSTTProvider):
        """Test all valid formats."""
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "results": {
                "channels": [{"alternatives": [{"transcript": "test"}]}],
                "metadata": {"duration": 1.0},
            }
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        formats = ["mp3", "wav", "ogg", "flac", "webm", "m4a"]
        for fmt in formats:
            result = await provider.transcribe(b"audio", fmt)
            assert result["text"] == "test"

    @pytest.mark.asyncio
    async def test_transcribe_with_timestamps(self, provider: DeepgramSTTProvider):
        """Test transcription with timestamps."""
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "results": {
                "channels": [
                    {
                        "alternatives": [
                            {
                                "transcript": "Hello world",
                                "words": [
                                    {"word": "Hello", "start": 0.0, "end": 0.5, "confidence": 0.95},
                                    {"word": "world", "start": 0.5, "end": 1.0, "confidence": 0.95},
                                ],
                            }
                        ]
                    }
                ],
                "metadata": {"duration": 1.0},
            }
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.transcribe(b"audio", "mp3", include_timestamps=True)
        assert result["words"] is not None
        assert len(result["words"]) == 2
        assert result["words"][0]["word"] == "Hello"
        assert result["words"][0]["start"] == 0.0

    @pytest.mark.asyncio
    async def test_transcribe_no_results_raises_error(self, provider: DeepgramSTTProvider):
        """Test no results raises RuntimeError."""
        mock_response = MagicMock()
        mock_response.json.return_value = {"results": {}}
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        with pytest.raises(RuntimeError, match="No transcription results"):
            await provider.transcribe(b"audio", "mp3")

    @pytest.mark.asyncio
    async def test_transcribe_no_alternatives_raises_error(self, provider: DeepgramSTTProvider):
        """Test no alternatives raises RuntimeError."""
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "results": {"channels": [{}]}
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        with pytest.raises(RuntimeError, match="No transcription alternatives"):
            await provider.transcribe(b"audio", "mp3")

    @pytest.mark.asyncio
    async def test_transcribe_http_error_raises_runtime_error(self, provider: DeepgramSTTProvider):
        """Test HTTP error raises RuntimeError."""
        mock_response = MagicMock()
        mock_response.raise_for_status = MagicMock(side_effect=Exception("HTTP 500"))
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        with pytest.raises(RuntimeError, match="Transcription failed"):
            await provider.transcribe(b"audio", "mp3")

    def test_estimate_cost(self, provider: DeepgramSTTProvider):
        """Test cost estimation."""
        cost = provider.estimate_cost(60.0)  # 1 minute
        assert cost > 0
        assert isinstance(cost, float)

    def test_estimate_cost_different_models(self, provider: DeepgramSTTProvider):
        """Test cost estimation for different models."""
        cost_nova2 = provider.estimate_cost(60.0)
        provider.model = "nova-2-phonecall"
        cost_phonecall = provider.estimate_cost(60.0)
        # Should be same pricing
        assert cost_nova2 == cost_phonecall

    def test_custom_base_url(self):
        """Test custom base URL."""
        provider = DeepgramSTTProvider(
            api_key="test_key",
            base_url="https://custom.example.com/v1",
        )
        assert provider.base_url == "https://custom.example.com/v1"


class TestMockSTTProvider:
    """Deep comprehensive tests for MockSTTProvider."""

    @pytest.fixture
    def provider(self):
        """Create Mock STT provider instance."""
        return MockSTTProvider(mock_transcript="Hello world")

    @pytest.mark.asyncio
    async def test_transcribe_returns_mock_transcript(self, provider: MockSTTProvider):
        """Test transcribe returns mock transcript."""
        result = await provider.transcribe(b"audio_data", "mp3")
        assert result["text"] == "Hello world"
        assert result["confidence"] == 1.0
        assert result["cost_usd"] == 0.0

    @pytest.mark.asyncio
    async def test_transcribe_with_timestamps(self, provider: MockSTTProvider):
        """Test transcribe with timestamps."""
        result = await provider.transcribe(b"audio", "mp3", include_timestamps=True)
        assert result["words"] is not None
        assert len(result["words"]) == 2
        assert result["words"][0]["word"] == "Hello"
        assert result["words"][0]["start"] == 0.0

    @pytest.mark.asyncio
    async def test_transcribe_without_timestamps(self, provider: MockSTTProvider):
        """Test transcribe without timestamps."""
        result = await provider.transcribe(b"audio", "mp3", include_timestamps=False)
        assert result["words"] is None

    @pytest.mark.asyncio
    async def test_transcribe_ignores_parameters(self, provider: MockSTTProvider):
        """Test transcribe ignores audio_data, format, language."""
        result1 = await provider.transcribe(b"audio1", "mp3", language="en")
        result2 = await provider.transcribe(b"audio2", "wav", language="es")
        # Should return same transcript regardless
        assert result1["text"] == result2["text"]

    def test_estimate_cost_always_zero(self, provider: MockSTTProvider):
        """Test estimate_cost always returns zero."""
        cost = provider.estimate_cost(60.0)
        assert cost == 0.0


class TestCreateSTTProvider:
    """Deep comprehensive tests for create_stt_provider factory."""

    def test_create_openai_provider(self):
        """Test creating OpenAI provider."""
        provider = create_stt_provider("openai", api_key="test_key")
        assert isinstance(provider, OpenAIWhisperProvider)
        assert provider.api_key == "test_key"

    def test_create_openai_provider_missing_key_raises_error(self):
        """Test creating OpenAI provider without key raises ValueError."""
        with pytest.raises(ValueError, match="api_key is required"):
            create_stt_provider("openai")

    def test_create_deepgram_provider(self):
        """Test creating Deepgram provider."""
        provider = create_stt_provider("deepgram", api_key="test_key")
        assert isinstance(provider, DeepgramSTTProvider)
        assert provider.api_key == "test_key"

    def test_create_deepgram_provider_missing_key_raises_error(self):
        """Test creating Deepgram provider without key raises ValueError."""
        with pytest.raises(ValueError, match="api_key is required"):
            create_stt_provider("deepgram")

    def test_create_mock_provider(self):
        """Test creating Mock provider."""
        provider = create_stt_provider("mock")
        assert isinstance(provider, MockSTTProvider)

    def test_create_mock_provider_with_custom_transcript(self):
        """Test creating Mock provider with custom transcript."""
        provider = create_stt_provider("mock", mock_transcript="Custom transcript")
        assert provider.mock_transcript == "Custom transcript"

    def test_create_unknown_provider_raises_error(self):
        """Test creating unknown provider raises ValueError."""
        with pytest.raises(ValueError, match="Unknown provider"):
            create_stt_provider("unknown")

    def test_create_provider_with_custom_params(self):
        """Test creating provider with custom parameters."""
        provider = create_stt_provider(
            "openai",
            api_key="test_key",
            model="whisper-1",
            base_url="https://custom.example.com",
        )
        assert provider.model == "whisper-1"
        assert provider.base_url == "https://custom.example.com"


class TestBugDetection:
    """Bug detection tests for STT providers."""

    @pytest.mark.asyncio
    async def test_bug_openai_may_not_detect_language_correctly(self):
        """BUG: OpenAI may not detect language correctly."""
        # Language detection may be inaccurate
        # This test documents the potential issue
        # TODO: Add test to verify language detection accuracy

    @pytest.mark.asyncio
    async def test_bug_deepgram_response_may_not_have_expected_structure(self):
        """BUG: Deepgram response may not have expected structure."""
        # API response structure may vary
        # This test documents the potential issue
        # TODO: Add test with various response structures

    @pytest.mark.asyncio
    async def test_bug_cost_estimation_may_not_be_accurate(self):
        """BUG: Cost estimation may not be accurate."""
        # Pricing may change or estimates may be off
        # This test documents the potential issue
        # TODO: Add test to verify cost accuracy

    @pytest.mark.asyncio
    async def test_bug_http_timeout_may_not_be_handled(self):
        """BUG: HTTP timeout may not be handled correctly."""
        # Timeouts may not be caught or retried
        # This test documents the potential issue
        # TODO: Add test with timeout scenarios

    @pytest.mark.asyncio
    async def test_bug_large_audio_may_cause_memory_issues(self):
        """BUG: Large audio may cause memory issues."""
        # Very large audio files may not be handled correctly
        # This test documents the potential issue
        # TODO: Add test with very large audio files
