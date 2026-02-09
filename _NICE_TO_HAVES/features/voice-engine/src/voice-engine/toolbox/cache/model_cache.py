"""
Model Cache - Cache loaded TTS/STT models in memory.

Prevents reloading models on every request.
Uses LRU eviction when memory limit reached.
"""

from __future__ import annotations

import logging
from collections import OrderedDict
from typing import Generic, TypeVar

logger = logging.getLogger(__name__)

T = TypeVar("T")


class ModelCache(Generic[T]):
    """
    LRU cache for model instances.
    
    Caches loaded models to avoid reloading on every request.
    Evicts least recently used models when size limit reached.
    """

    def __init__(self, max_size: int = 3) -> None:
        """
        Initialize model cache.
        
        Args:
            max_size: Maximum number of models to cache
        """
        self.max_size = max_size
        self._cache: OrderedDict[str, T] = OrderedDict()
        self._hits = 0
        self._misses = 0

    def get(self, key: str) -> T | None:
        """
        Get cached model.
        
        Args:
            key: Model identifier (e.g., "qwen3-tts-customvoice")
        
        Returns:
            Cached model or None if not found
        """
        if key in self._cache:
            # Move to end (most recently used)
            model = self._cache.pop(key)
            self._cache[key] = model
            self._hits += 1
            logger.debug(f"Model cache HIT: {key}")
            return model
        
        self._misses += 1
        logger.debug(f"Model cache MISS: {key}")
        return None

    def put(self, key: str, model: T) -> None:
        """
        Cache a model.
        
        Args:
            key: Model identifier
            model: Model instance to cache
        """
        # Remove if already exists
        if key in self._cache:
            self._cache.pop(key)
        
        # Add to end
        self._cache[key] = model
        
        # Evict if over limit
        if len(self._cache) > self.max_size:
            oldest_key, _ = self._cache.popitem(last=False)
            logger.debug(f"Model cache evicted: {oldest_key}")
    
    def clear(self) -> None:
        """Clear all cached models."""
        self._cache.clear()
        logger.info("Model cache cleared")
    
    def stats(self) -> dict[str, int | float]:
        """Get cache statistics."""
        total = self._hits + self._misses
        hit_rate = (self._hits / total * 100) if total > 0 else 0.0
        
        return {
            "size": len(self._cache),
            "max_size": self.max_size,
            "hits": self._hits,
            "misses": self._misses,
            "hit_rate": hit_rate,
        }


# Global model cache instance
_model_cache: ModelCache[object] | None = None


def get_model_cache() -> ModelCache[object]:
    """Get global model cache instance."""
    global _model_cache
    if _model_cache is None:
        max_size = int(__import__("os").getenv("MODEL_CACHE_SIZE", "3"))
        _model_cache = ModelCache(max_size=max_size)
    return _model_cache


__all__ = ["ModelCache", "get_model_cache"]
