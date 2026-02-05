"""
Deep comprehensive tests for VeniceChatEngine.

Tests API integration, caching, error handling, conversation creation, and bug detection.
"""
import os
import pytest
from unittest.mock import AsyncMock, MagicMock, patch
import httpx
from toolbox.engines.chatbot.venice_chat import (
    VeniceChatEngine,
    ChatMessage,
    ChatError,
)


class TestVeniceChatEngineInit:
    """Deep comprehensive tests for VeniceChatEngine initialization."""

    def test_init_with_api_key(self):
        """Test initialization with explicit API key."""
        engine = VeniceChatEngine(api_key="test-key")
        assert engine.api_key == "test-key"
        assert engine.base_url == "https://api.venice.ai/api/v1"

    def test_init_with_custom_base_url(self):
        """Test initialization with custom base URL."""
        engine = VeniceChatEngine(
            api_key="test-key",
            base_url="https://custom.venice.ai/api/v1",
        )
        assert engine.base_url == "https://custom.venice.ai/api/v1"

    def test_init_from_env(self):
        """Test initialization from environment variable."""
        with patch.dict(os.environ, {"VENICE_API_KEY": "env-key"}):
            engine = VeniceChatEngine()
            assert engine.api_key == "env-key"

    def test_init_no_api_key_raises_error(self):
        """Test initialization without API key raises ValueError."""
        with patch.dict(os.environ, {}, clear=True):
            with pytest.raises(ValueError, match="VENICE_API_KEY is required"):
                VeniceChatEngine()

    def test_init_client_not_created(self):
        """Test client is not created on initialization."""
        engine = VeniceChatEngine(api_key="test-key")
        assert engine._client is None


class TestVeniceChatEngineGetClient:
    """Deep comprehensive tests for _get_client method."""

    @pytest.mark.asyncio
    async def test_get_client_creates_client(self):
        """Test _get_client creates client on first call."""
        engine = VeniceChatEngine(api_key="test-key")
        client = engine._get_client()
        assert isinstance(client, httpx.AsyncClient)
        assert engine._client is not None

    @pytest.mark.asyncio
    async def test_get_client_reuses_client(self):
        """Test _get_client reuses existing client."""
        engine = VeniceChatEngine(api_key="test-key")
        client1 = engine._get_client()
        client2 = engine._get_client()
        assert client1 is client2

    @pytest.mark.asyncio
    async def test_get_client_sets_headers(self):
        """Test _get_client sets correct headers."""
        engine = VeniceChatEngine(api_key="test-key")
        client = engine._get_client()
        assert client.headers["Authorization"] == "Bearer test-key"
        assert client.headers["Content-Type"] == "application/json"

    @pytest.mark.asyncio
    async def test_get_client_sets_timeout(self):
        """Test _get_client sets timeout."""
        engine = VeniceChatEngine(api_key="test-key")
        client = engine._get_client()
        assert client.timeout == 180.0


class TestVeniceChatEngineSendMessage:
    """Deep comprehensive tests for send_message method."""

    @pytest.mark.asyncio
    async def test_send_message_success(self):
        """Test send_message with successful response."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [
                {
                    "message": {"content": "Hello, how can I help?"},
                    "finish_reason": "stop",
                }
            ],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
        )
        
        assert message is not None
        assert error is None
        assert message["role"] == "assistant"
        assert message["content"] == "Hello, how can I help?"
        assert message["tokens"] == 50
        assert message["conversation_id"] == "conv-123"

    @pytest.mark.asyncio
    async def test_send_message_with_thinking_block(self):
        """Test send_message extracts thinking blocks."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [
                {
                    "message": {
                        "content": "<think>reasoning</think>Hello, how can I help?",
                    },
                    "finish_reason": "stop",
                }
            ],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
        )
        
        assert message is not None
        assert message["metadata"]["thinking"] == "reasoning"

    @pytest.mark.asyncio
    async def test_send_message_with_custom_model(self):
        """Test send_message with custom model."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "Response"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o-mini",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
            model="gpt-4o-mini",
        )
        
        assert message is not None
        assert mock_client.post.call_args[1]["json"]["model"] == "gpt-4o-mini"

    @pytest.mark.asyncio
    async def test_send_message_with_custom_temperature(self):
        """Test send_message with custom temperature."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "Response"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
            temperature=0.9,
        )
        
        assert message is not None
        assert mock_client.post.call_args[1]["json"]["temperature"] == 0.9

    @pytest.mark.asyncio
    async def test_send_message_with_custom_max_tokens(self):
        """Test send_message with custom max_tokens."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "Response"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
            max_tokens=2048,
        )
        
        assert message is not None
        assert mock_client.post.call_args[1]["json"]["max_tokens"] == 2048

    @pytest.mark.asyncio
    async def test_send_message_no_choices_returns_error(self):
        """Test send_message with no choices returns error."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [],
            "usage": {"total_tokens": 50},
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
        )
        
        assert message is None
        assert error is not None
        assert error["code"] == "no_response"

    @pytest.mark.asyncio
    async def test_send_message_http_error(self):
        """Test send_message handles HTTP errors."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.status_code = 500
        mock_response.text = "Internal Server Error"
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(
            side_effect=httpx.HTTPStatusError(
                "Server Error",
                request=MagicMock(),
                response=mock_response,
            )
        )
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
        )
        
        assert message is None
        assert error is not None
        assert error["code"] == "api_error"
        assert "500" in error["message"]

    @pytest.mark.asyncio
    async def test_send_message_general_exception(self):
        """Test send_message handles general exceptions."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(side_effect=Exception("Network error"))
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
        )
        
        assert message is None
        assert error is not None
        assert error["code"] == "internal_error"

    @pytest.mark.asyncio
    async def test_send_message_uses_cache(self):
        """Test send_message uses response cache."""
        engine = VeniceChatEngine(api_key="test-key")
        
        cached_message: ChatMessage = {
            "id": "cached-msg",
            "conversation_id": "conv-123",
            "role": "assistant",
            "content": "Cached response",
            "tokens": 10,
            "metadata": {},
            "created_at": "2024-01-01T00:00:00Z",
        }
        
        with patch("toolbox.engines.chatbot.venice_chat.get_response_cache") as mock_get_cache:
            mock_cache = MagicMock()
            mock_cache.get = MagicMock(return_value=cached_message)
            mock_get_cache.return_value = mock_cache
            
            message, error = await engine.send_message(
                conversation_id="conv-123",
                user_id="user-123",
                content="Hello",
            )
            
            assert message == cached_message
            assert error is None
            mock_cache.get.assert_called_once()

    @pytest.mark.asyncio
    async def test_send_message_caches_response(self):
        """Test send_message caches response."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "Response"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        with patch("toolbox.engines.chatbot.venice_chat.get_response_cache") as mock_get_cache:
            mock_cache = MagicMock()
            mock_cache.get = MagicMock(return_value=None)
            mock_get_cache.return_value = mock_cache
            
            message, error = await engine.send_message(
                conversation_id="conv-123",
                user_id="user-123",
                content="Hello",
            )
            
            assert message is not None
            mock_cache.put.assert_called_once()

    @pytest.mark.asyncio
    async def test_send_message_default_model_from_env(self):
        """Test send_message uses default model from env."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "Response"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o-mini",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        with patch.dict(os.environ, {"VENICE_MODEL": "gpt-4o-mini"}):
            message, error = await engine.send_message(
                conversation_id="conv-123",
                user_id="user-123",
                content="Hello",
            )
            
            assert message is not None
            assert mock_client.post.call_args[1]["json"]["model"] == "gpt-4o-mini"

    @pytest.mark.asyncio
    async def test_send_message_analyst_role_ignored(self):
        """Test analyst_role parameter is ignored."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "Response"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="Hello",
            analyst_role="content_strategist",
        )
        
        # Should succeed even with analyst_role (ignored)
        assert message is not None


class TestVeniceChatEngineCreateConversation:
    """Deep comprehensive tests for create_conversation method."""

    @pytest.mark.asyncio
    async def test_create_conversation_basic(self):
        """Test create_conversation creates conversation."""
        engine = VeniceChatEngine(api_key="test-key")
        
        conversation = await engine.create_conversation(
            org_id="org-123",
            user_id="user-123",
        )
        
        assert conversation["org_id"] == "org-123"
        assert conversation["user_id"] == "user-123"
        assert conversation["channel"] == "voice"
        assert conversation["status"] == "active"
        assert "id" in conversation
        assert "created_at" in conversation
        assert "updated_at" in conversation

    @pytest.mark.asyncio
    async def test_create_conversation_with_custom_channel(self):
        """Test create_conversation with custom channel."""
        engine = VeniceChatEngine(api_key="test-key")
        
        conversation = await engine.create_conversation(
            org_id="org-123",
            user_id="user-123",
            channel="web",
        )
        
        assert conversation["channel"] == "web"

    @pytest.mark.asyncio
    async def test_create_conversation_deterministic_id(self):
        """Test create_conversation creates deterministic ID."""
        engine = VeniceChatEngine(api_key="test-key")
        
        conv1 = await engine.create_conversation(
            org_id="org-123",
            user_id="user-123",
            channel="voice",
        )
        
        conv2 = await engine.create_conversation(
            org_id="org-123",
            user_id="user-123",
            channel="voice",
        )
        
        # Same inputs should produce same ID
        assert conv1["id"] == conv2["id"]

    @pytest.mark.asyncio
    async def test_create_conversation_different_ids(self):
        """Test create_conversation creates different IDs for different inputs."""
        engine = VeniceChatEngine(api_key="test-key")
        
        conv1 = await engine.create_conversation(
            org_id="org-123",
            user_id="user-123",
            channel="voice",
        )
        
        conv2 = await engine.create_conversation(
            org_id="org-456",
            user_id="user-123",
            channel="voice",
        )
        
        # Different org_id should produce different ID
        assert conv1["id"] != conv2["id"]


class TestVeniceChatEngineClose:
    """Deep comprehensive tests for close method."""

    @pytest.mark.asyncio
    async def test_close_closes_client(self):
        """Test close closes HTTP client."""
        engine = VeniceChatEngine(api_key="test-key")
        mock_client = AsyncMock()
        engine._client = mock_client
        
        await engine.close()
        
        mock_client.aclose.assert_called_once()
        assert engine._client is None

    @pytest.mark.asyncio
    async def test_close_no_client(self):
        """Test close handles no client gracefully."""
        engine = VeniceChatEngine(api_key="test-key")
        engine._client = None
        
        # Should not raise
        await engine.close()
        
        assert engine._client is None


class TestEdgeCases:
    """Edge case tests for VeniceChatEngine."""

    @pytest.mark.asyncio
    async def test_send_message_empty_content(self):
        """Test send_message with empty content."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": ""}}],
            "usage": {"total_tokens": 0},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="",
        )
        
        assert message is not None
        assert message["content"] == ""

    @pytest.mark.asyncio
    async def test_send_message_very_long_content(self):
        """Test send_message with very long content."""
        engine = VeniceChatEngine(api_key="test-key")
        
        long_content = "Hello " * 10000
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "Response"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content=long_content,
        )
        
        assert message is not None

    @pytest.mark.asyncio
    async def test_send_message_unicode_content(self):
        """Test send_message with Unicode content."""
        engine = VeniceChatEngine(api_key="test-key")
        
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "id": "msg-123",
            "choices": [{"message": {"content": "你好"}}],
            "usage": {"total_tokens": 50},
            "model": "gpt-4o",
            "created": "2024-01-01T00:00:00Z",
        }
        mock_response.raise_for_status = MagicMock()
        
        mock_client = AsyncMock()
        mock_client.post = AsyncMock(return_value=mock_response)
        engine._client = mock_client
        
        message, error = await engine.send_message(
            conversation_id="conv-123",
            user_id="user-123",
            content="你好",
        )
        
        assert message is not None
        assert message["content"] == "你好"


class TestBugDetection:
    """Bug detection tests for VeniceChatEngine."""

    def test_bug_client_may_not_be_reused_correctly(self):
        """BUG: Client may not be reused correctly."""
        # Client may be recreated unnecessarily
        # This test documents the potential issue
        # TODO: Add test to verify client reuse

    def test_bug_cache_may_not_handle_analyst_role(self):
        """BUG: Cache may not handle analyst_role correctly."""
        # Cache key may not include analyst_role
        # This test documents the potential issue
        # TODO: Add test to verify cache key includes analyst_role

    def test_bug_thinking_extraction_may_fail_on_partial_tags(self):
        """BUG: Thinking extraction may fail on partial tags."""
        # Partial <think> tags may not be extracted correctly
        # This test documents the potential issue
        # TODO: Add test with partial think tags

    def test_bug_error_messages_may_not_be_user_friendly(self):
        """BUG: Error messages may not be user-friendly."""
        # API error messages may expose internal details
        # This test documents the potential issue
        # TODO: Add test to verify error message format

    def test_bug_timeout_may_not_be_configurable(self):
        """BUG: Timeout may not be configurable."""
        # Timeout is hardcoded to 180.0
        # This test documents the potential issue
        # TODO: Add test with configurable timeout
