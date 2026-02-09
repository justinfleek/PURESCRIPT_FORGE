"""
Deep comprehensive tests for TTS providers (API clients).

Tests OpenAI, ElevenLabs, Mock providers, factory function, and bug detection.
"""
import pytest
from unittest.mock import AsyncMock, MagicMock, patch
from toolbox.engines.voice_tts_providers import (
    OpenAITTSProvider,
    ElevenLabsTTSProvider,
    MockTTSProvider,
    create_tts_provider,
)


class TestOpenAITTSProvider:
    """Deep comprehensive tests for OpenAITTSProvider."""

    @pytest.fixture
    def provider(self):
        """Create OpenAI TTS provider instance."""
        return OpenAITTSProvider(
            api_key="test_key",
            model="tts-1",
            default_voice="alloy",
        )

    @pytest.mark.asyncio
    async def test_synthesize_basic(self, provider: OpenAITTSProvider):
        """Test basic synthesis."""
        mock_response = MagicMock()
        mock_response.content = b"mock_audio_data"
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        
        provider._client = mock_client
        
        result = await provider.synthesize("Hello, world!", "alloy")
        assert result == b"mock_audio_data"
        mock_client.post.assert_called_once()

    @pytest.mark.asyncio
    async def test_synthesize_uses_default_voice(self, provider: OpenAITTSProvider):
        """Test synthesize uses default voice when None provided."""
        mock_response = MagicMock()
        mock_response.content = b"audio"
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        await provider.synthesize("test", None)
        
        # Check that default voice was used
        call_args = mock_client.post.call_args
        assert call_args[1]["json"]["voice"] == "alloy"

    @pytest.mark.asyncio
    async def test_synthesize_invalid_voice_raises_error(self, provider: OpenAITTSProvider):
        """Test invalid voice raises ValueError."""
        with pytest.raises(ValueError, match="Invalid voice"):
            await provider.synthesize("test", "invalid_voice")

    @pytest.mark.asyncio
    async def test_synthesize_invalid_model_raises_error(self, provider: OpenAITTSProvider):
        """Test invalid model raises ValueError."""
        with pytest.raises(ValueError, match="Invalid model"):
            await provider.synthesize("test", "alloy", model="invalid_model")

    @pytest.mark.asyncio
    async def test_synthesize_invalid_format_raises_error(self, provider: OpenAITTSProvider):
        """Test invalid format raises ValueError."""
        with pytest.raises(ValueError, match="Invalid format"):
            await provider.synthesize("test", "alloy", format="invalid_format")

    @pytest.mark.asyncio
    async def test_synthesize_all_valid_formats(self, provider: OpenAITTSProvider):
        """Test all valid formats."""
        mock_response = MagicMock()
        mock_response.content = b"audio"
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        formats = ["mp3", "opus", "aac", "flac", "wav", "pcm"]
        for fmt in formats:
            await provider.synthesize("test", "alloy", format=fmt)
            call_args = mock_client.post.call_args
            assert call_args[1]["json"]["response_format"] == fmt

    @pytest.mark.asyncio
    async def test_synthesize_speed_parameter(self, provider: OpenAITTSProvider):
        """Test speed parameter is passed correctly."""
        mock_response = MagicMock()
        mock_response.content = b"audio"
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        await provider.synthesize("test", "alloy", speed=1.5)
        
        call_args = mock_client.post.call_args
        assert call_args[1]["json"]["speed"] == 1.5

    @pytest.mark.asyncio
    async def test_synthesize_http_error_raises_runtime_error(self, provider: OpenAITTSProvider):
        """Test HTTP error raises RuntimeError."""
        mock_response = MagicMock()
        mock_response.raise_for_status = MagicMock(side_effect=Exception("HTTP 500"))
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        with pytest.raises(RuntimeError, match="TTS synthesis failed"):
            await provider.synthesize("test", "alloy")

    @pytest.mark.asyncio
    async def test_synthesize_custom_model(self, provider: OpenAITTSProvider):
        """Test custom model parameter."""
        mock_response = MagicMock()
        mock_response.content = b"audio"
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        await provider.synthesize("test", "alloy", model="tts-1-hd")
        
        call_args = mock_client.post.call_args
        assert call_args[1]["json"]["model"] == "tts-1-hd"

    def test_get_available_voices(self, provider: OpenAITTSProvider):
        """Test get_available_voices returns all voices."""
        voices = provider.get_available_voices()
        assert len(voices) == 6
        assert "alloy" in voices
        assert "echo" in voices
        assert "fable" in voices
        assert "onyx" in voices
        assert "nova" in voices
        assert "shimmer" in voices

    def test_estimate_cost(self, provider: OpenAITTSProvider):
        """Test cost estimation."""
        cost = provider.estimate_cost("Hello, world!")
        assert cost > 0
        assert isinstance(cost, float)

    def test_estimate_cost_different_models(self, provider: OpenAITTSProvider):
        """Test cost estimation for different models."""
        cost_tts1 = provider.estimate_cost("test", model="tts-1")
        cost_tts1hd = provider.estimate_cost("test", model="tts-1-hd")
        assert cost_tts1hd > cost_tts1  # HD should be more expensive

    def test_estimate_cost_empty_text(self, provider: OpenAITTSProvider):
        """Test cost estimation for empty text."""
        cost = provider.estimate_cost("")
        assert cost == 0.0

    def test_custom_base_url(self):
        """Test custom base URL."""
        provider = OpenAITTSProvider(
            api_key="test_key",
            base_url="https://custom.example.com/v1",
        )
        assert provider.base_url == "https://custom.example.com/v1"

    @pytest.mark.asyncio
    async def test_lazy_client_loading(self, provider: OpenAITTSProvider):
        """Test client is lazily loaded."""
        assert provider._client is None
        # Accessing _get_client should create client
        with patch("httpx.AsyncClient") as mock_client_class:
            mock_client = AsyncMock()
            mock_client_class.return_value = mock_client
            client = provider._get_client()
            assert client is not None
            mock_client_class.assert_called_once()

    @pytest.mark.asyncio
    async def test_httpx_not_installed_raises_error(self, provider: OpenAITTSProvider):
        """Test ImportError when httpx not installed."""
        with patch("builtins.__import__", side_effect=ImportError("No module named httpx")):
            with pytest.raises(ImportError, match="httpx is required"):
                provider._get_client()

    @pytest.mark.asyncio
    async def test_bug_client_may_not_be_reused(self, provider: OpenAITTSProvider):
        """BUG: Client may not be reused correctly."""
        # Multiple calls should reuse same client
        # BUG: Client may be recreated unnecessarily
        # This test documents the potential issue
        # TODO: Add test to verify client reuse


class TestElevenLabsTTSProvider:
    """Deep comprehensive tests for ElevenLabsTTSProvider."""

    @pytest.fixture
    def provider(self):
        """Create ElevenLabs TTS provider instance."""
        return ElevenLabsTTSProvider(
            api_key="test_key",
            model="eleven_monolingual_v1",
            default_voice="21m00Tcm4TlvDq8ikWAM",
        )

    @pytest.mark.asyncio
    async def test_synthesize_basic(self, provider: ElevenLabsTTSProvider):
        """Test basic synthesis."""
        mock_response = MagicMock()
        mock_response.content = b"mock_audio_data"
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        result = await provider.synthesize("Hello, world!", "21m00Tcm4TlvDq8ikWAM")
        assert result == b"mock_audio_data"
        mock_client.post.assert_called_once()

    @pytest.mark.asyncio
    async def test_synthesize_speed_validation(self, provider: ElevenLabsTTSProvider):
        """Test speed validation."""
        # Too low
        with pytest.raises(ValueError, match="Speed must be"):
            await provider.synthesize("test", "voice", speed=0.2)
        
        # Too high
        with pytest.raises(ValueError, match="Speed must be"):
            await provider.synthesize("test", "voice", speed=5.0)
        
        # Valid range
        mock_response = MagicMock()
        mock_response.content = b"audio"
        mock_response.raise_for_status = MagicMock()
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        await provider.synthesize("test", "voice", speed=2.0)
        # Should succeed

    @pytest.mark.asyncio
    async def test_synthesize_format_mapping(self, provider: ElevenLabsTTSProvider):
        """Test format mapping."""
        mock_response = MagicMock()
        mock_response.content = b"audio"
        mock_response.raise_for_status = MagicMock()
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        # Format mapping is internal, but request should succeed
        await provider.synthesize("test", "voice", format="mp3")
        mock_client.post.assert_called_once()

    @pytest.mark.asyncio
    async def test_synthesize_http_error_raises_runtime_error(self, provider: ElevenLabsTTSProvider):
        """Test HTTP error raises RuntimeError."""
        mock_response = MagicMock()
        mock_response.raise_for_status = MagicMock(side_effect=Exception("HTTP 500"))
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        with pytest.raises(RuntimeError, match="TTS synthesis failed"):
            await provider.synthesize("test", "voice")

    def test_get_available_voices_returns_default(self, provider: ElevenLabsTTSProvider):
        """Test get_available_voices returns default when cache not populated."""
        voices = provider.get_available_voices()
        assert voices == [provider.default_voice]

    @pytest.mark.asyncio
    async def test_fetch_voices(self, provider: ElevenLabsTTSProvider):
        """Test fetch_voices populates cache."""
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "voices": [
                {"voice_id": "voice1"},
                {"voice_id": "voice2"},
            ]
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.get = AsyncMock(return_value=mock_response)
        provider._client = mock_client
        
        voices = await provider.fetch_voices()
        assert len(voices) == 2
        assert "voice1" in voices
        assert "voice2" in voices
        
        # Cache should be populated
        assert provider.get_available_voices() == voices

    @pytest.mark.asyncio
    async def test_fetch_voices_error_returns_default(self, provider: ElevenLabsTTSProvider):
        """Test fetch_voices returns default on error."""
        mock_client = AsyncMock()
        mock_client.get = AsyncMock(side_effect=Exception("API error"))
        provider._client = mock_client
        
        voices = await provider.fetch_voices()
        assert voices == [provider.default_voice]

    def test_estimate_cost(self, provider: ElevenLabsTTSProvider):
        """Test cost estimation."""
        cost = provider.estimate_cost("Hello, world!")
        assert cost > 0
        assert isinstance(cost, float)

    def test_custom_base_url(self):
        """Test custom base URL."""
        provider = ElevenLabsTTSProvider(
            api_key="test_key",
            base_url="https://custom.example.com/v1",
        )
        assert provider.base_url == "https://custom.example.com/v1"


class TestMockTTSProvider:
    """Deep comprehensive tests for MockTTSProvider."""

    @pytest.fixture
    def provider(self):
        """Create Mock TTS provider instance."""
        return MockTTSProvider(default_voice="mock_voice_1")

    @pytest.mark.asyncio
    async def test_synthesize_returns_mock_audio(self, provider: MockTTSProvider):
        """Test synthesize returns mock audio."""
        result = await provider.synthesize("Hello, world!", "mock_voice_1")
        assert isinstance(result, bytes)
        assert b"ID3" in result  # Mock MP3 header
        assert b"Hello, world!" in result

    @pytest.mark.asyncio
    async def test_synthesize_ignores_parameters(self, provider: MockTTSProvider):
        """Test synthesize ignores model, speed, format parameters."""
        result1 = await provider.synthesize("test", "voice", model="model", speed=2.0, format="wav")
        result2 = await provider.synthesize("test", "voice")
        # Should return same format regardless of parameters
        assert isinstance(result1, bytes)
        assert isinstance(result2, bytes)

    def test_get_available_voices(self, provider: MockTTSProvider):
        """Test get_available_voices returns mock voices."""
        voices = provider.get_available_voices()
        assert len(voices) == 3
        assert "mock_voice_1" in voices
        assert "mock_voice_2" in voices
        assert "mock_voice_3" in voices

    def test_estimate_cost_always_zero(self, provider: MockTTSProvider):
        """Test estimate_cost always returns zero."""
        cost = provider.estimate_cost("any text")
        assert cost == 0.0


class TestCreateTTSProvider:
    """Deep comprehensive tests for create_tts_provider factory."""

    def test_create_openai_provider(self):
        """Test creating OpenAI provider."""
        provider = create_tts_provider("openai", api_key="test_key")
        assert isinstance(provider, OpenAITTSProvider)
        assert provider.api_key == "test_key"

    def test_create_openai_provider_missing_key_raises_error(self):
        """Test creating OpenAI provider without key raises ValueError."""
        with pytest.raises(ValueError, match="api_key is required"):
            create_tts_provider("openai")

    def test_create_elevenlabs_provider(self):
        """Test creating ElevenLabs provider."""
        provider = create_tts_provider("elevenlabs", api_key="test_key")
        assert isinstance(provider, ElevenLabsTTSProvider)
        assert provider.api_key == "test_key"

    def test_create_elevenlabs_provider_missing_key_raises_error(self):
        """Test creating ElevenLabs provider without key raises ValueError."""
        with pytest.raises(ValueError, match="api_key is required"):
            create_tts_provider("elevenlabs")

    def test_create_mock_provider(self):
        """Test creating Mock provider."""
        provider = create_tts_provider("mock")
        assert isinstance(provider, MockTTSProvider)

    def test_create_unknown_provider_raises_error(self):
        """Test creating unknown provider raises ValueError."""
        with pytest.raises(ValueError, match="Unknown provider"):
            create_tts_provider("unknown")

    def test_create_provider_with_custom_params(self):
        """Test creating provider with custom parameters."""
        provider = create_tts_provider(
            "openai",
            api_key="test_key",
            model="tts-1-hd",
            default_voice="nova",
            base_url="https://custom.example.com",
        )
        assert provider.model == "tts-1-hd"
        assert provider.default_voice == "nova"
        assert provider.base_url == "https://custom.example.com"


class TestBugDetection:
    """Bug detection tests for TTS providers."""

    @pytest.mark.asyncio
    async def test_bug_openai_api_may_not_handle_unicode(self):
        """BUG: OpenAI API may not handle Unicode correctly."""
        # Unicode text may cause issues
        # This test documents the potential issue
        # TODO: Add test with Unicode text

    @pytest.mark.asyncio
    async def test_bug_elevenlabs_voices_cache_may_not_update(self):
        """BUG: ElevenLabs voices cache may not update correctly."""
        # Cache may not refresh when voices change
        # This test documents the potential issue
        # TODO: Add test to verify cache refresh

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
