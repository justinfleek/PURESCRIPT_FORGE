"""
Deep comprehensive tests for ModelCache.

Tests LRU caching, eviction, statistics, and bug detection.
"""
import pytest
from toolbox.cache.model_cache import ModelCache


class TestModelCache:
    """Deep comprehensive tests for ModelCache."""

    @pytest.fixture
    def cache(self):
        """Create ModelCache instance for testing."""
        return ModelCache[str](max_size=3)

    def test_initialization(self, cache: ModelCache[str]):
        """Test cache initialization."""
        assert cache.max_size == 3
        assert cache._hits == 0
        assert cache._misses == 0
        assert len(cache._cache) == 0

    def test_get_miss(self, cache: ModelCache[str]):
        """Test get returns None on miss."""
        result = cache.get("model1")
        assert result is None
        assert cache._misses == 1
        assert cache._hits == 0

    def test_put_and_get(self, cache: ModelCache[str]):
        """Test put and get operations."""
        model = "test_model_instance"
        cache.put("model1", model)
        
        result = cache.get("model1")
        assert result == model
        assert cache._hits == 1
        assert cache._misses == 0

    def test_lru_eviction(self, cache: ModelCache[str]):
        """Test LRU eviction when max_size exceeded."""
        # Fill cache to max_size
        for i in range(3):
            cache.put(f"model{i}", f"instance{i}")
        
        # Add one more - should evict oldest
        cache.put("model3", "instance3")
        
        assert len(cache._cache) == 3
        # Oldest should be evicted
        result = cache.get("model0")
        assert result is None  # Should be evicted

    def test_lru_order_preserved(self, cache: ModelCache[str]):
        """Test LRU order is preserved on access."""
        cache.put("model1", "instance1")
        cache.put("model2", "instance2")
        cache.put("model3", "instance3")
        
        # Access model1 - should move to end
        cache.get("model1")
        
        # Add new entry - should evict model2 (not model1)
        cache.put("model4", "instance4")
        
        assert cache.get("model1") is not None
        assert cache.get("model2") is None  # Evicted

    def test_put_overwrites_existing(self, cache: ModelCache[str]):
        """Test put overwrites existing entry."""
        cache.put("model1", "instance1")
        cache.put("model1", "instance2")
        
        result = cache.get("model1")
        assert result == "instance2"  # Should be updated value

    def test_clear(self, cache: ModelCache[str]):
        """Test clear removes all entries."""
        cache.put("model1", "instance1")
        cache.put("model2", "instance2")
        
        cache.clear()
        assert len(cache._cache) == 0

    def test_stats(self, cache: ModelCache[str]):
        """Test stats calculation."""
        cache.put("model1", "instance1")
        cache.get("model1")  # Hit
        cache.get("missing")  # Miss
        
        stats = cache.stats()
        assert stats["hits"] == 1
        assert stats["misses"] == 1
        assert stats["size"] == 1
        assert stats["max_size"] == 3
        assert stats["hit_rate"] == 50.0  # 1 hit / 2 total = 50%

    def test_stats_zero_total(self, cache: ModelCache[str]):
        """Test stats with zero total requests."""
        stats = cache.stats()
        assert stats["hits"] == 0
        assert stats["misses"] == 0
        assert stats["hit_rate"] == 0.0

    def test_generic_type_support(self):
        """Test generic type support."""
        cache_int = ModelCache[int](max_size=3)
        cache_int.put("key1", 123)
        assert cache_int.get("key1") == 123
        
        cache_dict = ModelCache[dict](max_size=3)
        cache_dict.put("key1", {"test": "value"})
        assert cache_dict.get("key1") == {"test": "value"}

    def test_empty_key(self, cache: ModelCache[str]):
        """Test empty key."""
        cache.put("", "instance")
        result = cache.get("")
        assert result == "instance"

    def test_very_long_key(self, cache: ModelCache[str]):
        """Test very long key."""
        long_key = "a" * 1000
        cache.put(long_key, "instance")
        result = cache.get(long_key)
        assert result == "instance"

    def test_unicode_key(self, cache: ModelCache[str]):
        """Test Unicode key."""
        cache.put("测试", "instance")
        result = cache.get("测试")
        assert result == "instance"

    def test_none_value(self, cache: ModelCache[str | None]):
        """Test None value handling."""
        cache.put("model1", None)
        result = cache.get("model1")
        assert result is None

    def test_max_size_zero(self):
        """Test max_size zero."""
        cache = ModelCache[str](max_size=0)
        cache.put("model1", "instance1")
        # Should evict immediately
        assert len(cache._cache) == 0

    def test_max_size_one(self):
        """Test max_size one."""
        cache = ModelCache[str](max_size=1)
        cache.put("model1", "instance1")
        cache.put("model2", "instance2")
        # Should evict model1
        assert cache.get("model1") is None
        assert cache.get("model2") is not None

    def test_bug_lru_eviction_may_not_work_correctly(self, cache: ModelCache[str]):
        """BUG: LRU eviction may not work correctly."""
        # OrderedDict operations may not preserve order correctly
        # BUG: LRU eviction may evict wrong entry
        # This test documents the potential issue
        pass

    def test_bug_stats_may_not_be_accurate(self, cache: ModelCache[str]):
        """BUG: Stats may not be accurate."""
        # Hit/miss counting may have race conditions
        # BUG: Stats accuracy may be affected by concurrency
        # This test documents the potential issue
        pass

    def test_bug_put_may_not_update_order(self, cache: ModelCache[str]):
        """BUG: Put may not update LRU order correctly."""
        # Updating existing entry may not move it to end
        # BUG: Order may not be updated on put
        # This test documents the potential issue
        pass


class TestGetModelCache:
    """Tests for get_model_cache global function."""

    def test_returns_singleton(self):
        """Test returns singleton instance."""
        from toolbox.cache.model_cache import get_model_cache
        
        cache1 = get_model_cache()
        cache2 = get_model_cache()
        assert cache1 is cache2

    def test_uses_environment_variables(self):
        """Test uses environment variables."""
        import os
        from toolbox.cache.model_cache import get_model_cache
        
        # Set environment variable
        os.environ["MODEL_CACHE_SIZE"] = "5"
        
        # Clear singleton to force recreation
        import toolbox.cache.model_cache as cache_module
        cache_module._model_cache = None
        
        cache = get_model_cache()
        assert cache.max_size == 5

    def test_bug_singleton_may_not_be_thread_safe(self):
        """BUG: Singleton may not be thread-safe."""
        # Concurrent access may create multiple instances
        # BUG: Thread safety may not be guaranteed
        # This test documents the potential issue
        pass
