"""
Response Cache - Cache chat responses by conversation+query.

Caches LLM responses to avoid re-processing identical queries.
Uses hash of (conversation_id, query, analyst_role) as key.
"""

from __future__ import annotations

import hashlib
import json
import logging
from collections import OrderedDict
from datetime import datetime, timezone, timedelta

logger = logging.getLogger(__name__)


class ResponseCache:
    """
    TTL-based cache for chat responses.
    
    Caches LLM responses by conversation and query.
    Evicts entries after TTL expires.
    """

    def __init__(
        self,
        max_size: int = 5000,
        ttl_seconds: int = 1800,  # 30 minutes
    ) -> None:
        """
        Initialize response cache.
        
        Args:
            max_size: Maximum number of cached entries
            ttl_seconds: Time-to-live in seconds (default: 30 minutes)
        """
        self.max_size = max_size
        self.ttl_seconds = ttl_seconds
        self._cache: OrderedDict[str, tuple[dict, datetime]] = OrderedDict()
        self._hits = 0
        self._misses = 0

    def _make_key(
        self,
        conversation_id: str,
        query: str,
        analyst_role: str | None = None,
    ) -> str:
        """Generate cache key from conversation, query, and analyst."""
        content = f"{conversation_id}|{query}|{analyst_role or 'default'}"
        return hashlib.sha256(content.encode("utf-8")).hexdigest()

    def get(
        self,
        conversation_id: str,
        query: str,
        analyst_role: str | None = None,
    ) -> dict | None:
        """
        Get cached response.
        
        Args:
            conversation_id: Conversation ID
            query: User query
            analyst_role: Analyst role used
        
        Returns:
            Cached response dict or None if not found/expired
        """
        key = self._make_key(conversation_id, query, analyst_role)
        
        if key not in self._cache:
            self._misses += 1
            logger.debug(f"Response cache MISS: {key[:8]}...")
            return None
        
        response, cached_at = self._cache[key]
        
        # Check TTL
        age = (datetime.now(timezone.utc) - cached_at).total_seconds()
        if age > self.ttl_seconds:
            # Expired
            del self._cache[key]
            self._misses += 1
            logger.debug(f"Response cache EXPIRED: {key[:8]}...")
            return None
        
        # Move to end (most recently used)
        self._cache.pop(key)
        self._cache[key] = (response, cached_at)
        self._hits += 1
        logger.debug(f"Response cache HIT: {key[:8]}...")
        return response

    def put(
        self,
        conversation_id: str,
        query: str,
        response: dict,
        analyst_role: str | None = None,
    ) -> None:
        """
        Cache a response.
        
        Args:
            conversation_id: Conversation ID
            query: User query
            response: Response dict to cache
            analyst_role: Analyst role used
        """
        key = self._make_key(conversation_id, query, analyst_role)
        
        # Remove if already exists
        if key in self._cache:
            self._cache.pop(key)
        
        # Add to end
        self._cache[key] = (response, datetime.now(timezone.utc))
        
        # Evict if over limit
        if len(self._cache) > self.max_size:
            oldest_key, _ = self._cache.popitem(last=False)
            logger.debug(f"Response cache evicted: {oldest_key[:8]}...")
    
    def clear(self) -> None:
        """Clear all cached responses."""
        self._cache.clear()
        logger.info("Response cache cleared")
    
    def cleanup_expired(self) -> int:
        """
        Remove expired entries.
        
        Returns:
            Number of entries removed
        """
        now = datetime.now(timezone.utc)
        expired_keys = [
            key
            for key, (_, cached_at) in self._cache.items()
            if (now - cached_at).total_seconds() > self.ttl_seconds
        ]
        
        for key in expired_keys:
            del self._cache[key]
        
        if expired_keys:
            logger.info(f"Cleaned up {len(expired_keys)} expired response cache entries")
        
        return len(expired_keys)
    
    def stats(self) -> dict[str, int | float]:
        """Get cache statistics."""
        total = self._hits + self._misses
        hit_rate = (self._hits / total * 100) if total > 0 else 0.0
        
        # Count non-expired entries
        now = datetime.now(timezone.utc)
        valid_entries = sum(
            1
            for _, cached_at in self._cache.values()
            if (now - cached_at).total_seconds() <= self.ttl_seconds
        )
        
        return {
            "size": valid_entries,
            "max_size": self.max_size,
            "hits": self._hits,
            "misses": self._misses,
            "hit_rate": hit_rate,
            "ttl_seconds": self.ttl_seconds,
        }


# Global response cache instance
_response_cache: ResponseCache | None = None


def get_response_cache() -> ResponseCache:
    """Get global response cache instance."""
    global _response_cache
    if _response_cache is None:
        max_size = int(__import__("os").getenv("RESPONSE_CACHE_SIZE", "5000"))
        ttl = int(__import__("os").getenv("RESPONSE_CACHE_TTL_SECONDS", "1800"))
        _response_cache = ResponseCache(max_size=max_size, ttl_seconds=ttl)
    return _response_cache


__all__ = ["ResponseCache", "get_response_cache"]
