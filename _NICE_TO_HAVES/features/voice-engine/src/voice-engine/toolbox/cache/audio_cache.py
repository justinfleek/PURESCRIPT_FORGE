"""
Audio Cache - Cache synthesized audio by text+voice.

Caches TTS audio outputs to avoid re-synthesizing identical requests.
Uses hash of (text, voice, format) as key.
"""

from __future__ import annotations

import hashlib
import logging
from collections import OrderedDict
from datetime import datetime, timezone, timedelta

logger = logging.getLogger(__name__)


class AudioCache:
    """
    TTL-based cache for audio synthesis results.
    
    Caches audio bytes by hash of (text, voice, format).
    Evicts entries after TTL expires.
    """

    def __init__(
        self,
        max_size: int = 1000,
        ttl_seconds: int = 3600,
    ) -> None:
        """
        Initialize audio cache.
        
        Args:
            max_size: Maximum number of cached entries
            ttl_seconds: Time-to-live in seconds (default: 1 hour)
        """
        self.max_size = max_size
        self.ttl_seconds = ttl_seconds
        self._cache: OrderedDict[str, tuple[bytes, datetime]] = OrderedDict()
        self._hits = 0
        self._misses = 0

    def _make_key(self, text: str, voice: str, format: str) -> str:
        """Generate cache key from text, voice, and format."""
        content = f"{text}|{voice}|{format}"
        return hashlib.sha256(content.encode("utf-8")).hexdigest()

    def get(
        self,
        text: str,
        voice: str,
        format: str = "mp3",
    ) -> bytes | None:
        """
        Get cached audio.
        
        Args:
            text: Text that was synthesized
            voice: Voice used
            format: Audio format
        
        Returns:
            Cached audio bytes or None if not found/expired
        """
        key = self._make_key(text, voice, format)
        
        if key not in self._cache:
            self._misses += 1
            logger.debug(f"Audio cache MISS: {key[:8]}...")
            return None
        
        audio_bytes, cached_at = self._cache[key]
        
        # Check TTL
        age = (datetime.now(timezone.utc) - cached_at).total_seconds()
        if age > self.ttl_seconds:
            # Expired
            del self._cache[key]
            self._misses += 1
            logger.debug(f"Audio cache EXPIRED: {key[:8]}...")
            return None
        
        # Move to end (most recently used)
        self._cache.pop(key)
        self._cache[key] = (audio_bytes, cached_at)
        self._hits += 1
        logger.debug(f"Audio cache HIT: {key[:8]}...")
        return audio_bytes

    def put(
        self,
        text: str,
        voice: str,
        format: str,
        audio_bytes: bytes,
    ) -> None:
        """
        Cache audio.
        
        Args:
            text: Text that was synthesized
            voice: Voice used
            format: Audio format
            audio_bytes: Audio bytes to cache
        """
        key = self._make_key(text, voice, format)
        
        # Remove if already exists
        if key in self._cache:
            self._cache.pop(key)
        
        # Add to end
        self._cache[key] = (audio_bytes, datetime.now(timezone.utc))
        
        # Evict if over limit
        if len(self._cache) > self.max_size:
            oldest_key, _ = self._cache.popitem(last=False)
            logger.debug(f"Audio cache evicted: {oldest_key[:8]}...")
    
    def clear(self) -> None:
        """Clear all cached audio."""
        self._cache.clear()
        logger.info("Audio cache cleared")
    
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
            logger.info(f"Cleaned up {len(expired_keys)} expired audio cache entries")
        
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


# Global audio cache instance
_audio_cache: AudioCache | None = None


def get_audio_cache() -> AudioCache:
    """Get global audio cache instance."""
    global _audio_cache
    if _audio_cache is None:
        max_size = int(__import__("os").getenv("AUDIO_CACHE_SIZE", "1000"))
        ttl = int(__import__("os").getenv("AUDIO_CACHE_TTL_SECONDS", "3600"))
        _audio_cache = AudioCache(max_size=max_size, ttl_seconds=ttl)
    return _audio_cache


__all__ = ["AudioCache", "get_audio_cache"]
