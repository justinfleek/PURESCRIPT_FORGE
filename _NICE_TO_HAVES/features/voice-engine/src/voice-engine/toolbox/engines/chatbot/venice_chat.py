"""
Venice Chat Engine - Full integration with Venice API.

Implements ChatEngine protocol using Venice API client.
"""

from __future__ import annotations

import logging
import os
from typing import TypedDict

import httpx

logger = logging.getLogger(__name__)


class ChatMessage(TypedDict):
    """Chat message format."""
    id: str
    conversation_id: str
    role: str
    content: str
    tokens: int
    metadata: dict
    created_at: str


class ChatError(TypedDict):
    """Chat error format."""
    code: str
    message: str


class VeniceChatEngine:
    """
    Chat engine using Venice API.
    
    Implements ChatEngine protocol for voice chat integration.
    """

    def __init__(
        self,
        api_key: str | None = None,
        base_url: str = "https://api.venice.ai/api/v1",
    ) -> None:
        """
        Initialize Venice chat engine.

        Args:
            api_key: Venice API key (from env if not provided)
            base_url: Venice API base URL
        """
        self.api_key = api_key or os.getenv("VENICE_API_KEY", "")
        if not self.api_key:
            raise ValueError("VENICE_API_KEY is required")
        
        self.base_url = base_url
        self._client: httpx.AsyncClient | None = None

    def _get_client(self) -> httpx.AsyncClient:
        """Get or create HTTP client."""
        if self._client is None:
            self._client = httpx.AsyncClient(
                base_url=self.base_url,
                headers={
                    "Authorization": f"Bearer {self.api_key}",
                    "Content-Type": "application/json",
                },
                timeout=180.0,
            )
        return self._client

    async def send_message(
        self,
        conversation_id: str,
        user_id: str,
        content: str,
        analyst_role: str | None = None,
        **kwargs,
    ) -> tuple[ChatMessage | None, ChatError | None]:
        """
        Send message and get AI response.

        Args:
            conversation_id: Conversation ID
            user_id: User ID
            content: Message content
            analyst_role: Optional analyst role (ignored for Venice)
            **kwargs: Additional parameters

        Returns:
            Tuple of (message, error)
        """
        # Check response cache first
        from toolbox.cache import get_response_cache
        response_cache = get_response_cache()
        cached_response = response_cache.get(conversation_id, content, analyst_role)
        
        if cached_response is not None:
            logger.debug(f"Response cache HIT for conversation: {conversation_id}")
            return cached_response, None
        
        try:
            # Build messages (Venice uses OpenAI format)
            messages = [
                {
                    "role": "user",
                    "content": content,
                }
            ]

            # Get model from kwargs or use default
            model = kwargs.get("model", os.getenv("VENICE_MODEL", "gpt-4o"))
            temperature = kwargs.get("temperature", 0.7)
            max_tokens = kwargs.get("max_tokens", 4096)

            # Call Venice API
            client = self._get_client()
            response = await client.post(
                "/chat/completions",
                json={
                    "model": model,
                    "messages": messages,
                    "temperature": temperature,
                    "max_tokens": max_tokens,
                    "stream": False,
                },
            )

            response.raise_for_status()
            data = response.json()

            # Extract response
            choices = data.get("choices", [])
            if not choices:
                return None, ChatError(
                    code="no_response",
                    message="No response from Venice API",
                )

            choice = choices[0]
            message_content = choice.get("message", {}).get("content", "")
            usage = data.get("usage", {})
            tokens_used = usage.get("total_tokens", 0)

            # Extract thinking blocks if present
            thinking_content = None
            if "<think>" in message_content and "</think>" in message_content:
                from toolbox.llm.chat_template import extract_thinking
                _, thinking_content = extract_thinking(message_content)

            # Build message
            message: ChatMessage = {
                "id": data.get("id", f"msg_{conversation_id}"),
                "conversation_id": conversation_id,
                "role": "assistant",
                "content": message_content,
                "tokens": tokens_used,
                "metadata": {
                    "model": data.get("model", model),
                    "thinking": thinking_content,
                    "finish_reason": choice.get("finish_reason", "stop"),
                },
                "created_at": data.get("created", ""),
            }
            
            # Cache the response
            response_cache.put(conversation_id, content, message, analyst_role)
            logger.debug(f"Generated and cached response for conversation: {conversation_id}")

            return message, None

        except httpx.HTTPStatusError as e:
            logger.error(f"Venice API error: {e.response.status_code} - {e.response.text}")
            return None, ChatError(
                code="api_error",
                message=f"Venice API error: {e.response.status_code}",
            )
        except Exception as e:
            logger.error(f"Chat engine error: {e}")
            return None, ChatError(
                code="internal_error",
                message=str(e),
            )

    async def create_conversation(
        self,
        org_id: str,
        user_id: str,
        channel: str = "voice",
        **kwargs,
    ) -> dict:
        """
        Create a new conversation.

        Args:
            org_id: Organization ID
            user_id: User ID
            channel: Channel name
            **kwargs: Additional parameters

        Returns:
            Conversation dict
        """
        from toolbox.core.deterministic_id import make_uuid
        from datetime import timezone, datetime

        conversation_id = make_uuid("conversation", org_id, user_id, channel)
        
        return {
            "id": conversation_id,
            "org_id": org_id,
            "user_id": user_id,
            "channel": channel,
            "status": "active",
            "created_at": datetime.now(timezone.utc).isoformat(),
            "updated_at": datetime.now(timezone.utc).isoformat(),
        }

    async def close(self) -> None:
        """Close HTTP client."""
        if self._client:
            await self._client.aclose()
            self._client = None


__all__ = ["VeniceChatEngine", "ChatMessage", "ChatError"]
