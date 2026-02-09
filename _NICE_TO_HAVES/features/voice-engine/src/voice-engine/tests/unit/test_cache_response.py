"""
Deep comprehensive tests for ResponseCache.

Tests caching, TTL, eviction, statistics, and bug detection.
"""
import pytest
from datetime import datetime, timezone, timedelta
from toolbox.cache.response_cache import ResponseCache


class TestResponseCache:
    """Deep comprehensive tests for ResponseCache."""

    @pytest.fixture
    def cache(self):
        """Create ResponseCache instance for testing."""
        return ResponseCache(max_size=100, ttl_seconds=1800)

    def test_initialization(self, cache: ResponseCache):
        """Test cache initialization."""
        assert cache.max_size == 100
        assert cache.ttl_seconds == 1800
        assert cache._hits == 0
        assert cache._misses == 0
        assert len(cache._cache) == 0

    def test_get_miss(self, cache: ResponseCache):
        """Test get returns None on miss."""
        result = cache.get("conv1", "query", None)
        assert result is None
        assert cache._misses == 1
        assert cache._hits == 0

    def test_put_and_get(self, cache: ResponseCache):
        """Test put and get operations."""
        response = {"text": "Hello, world!", "tokens": 10}
        cache.put("conv1", "query", response)
        
        result = cache.get("conv1", "query", None)
        assert result == response
        assert cache._hits == 1
        assert cache._misses == 0

    def test_key_generation_deterministic(self, cache: ResponseCache):
        """Test key generation is deterministic."""
        key1 = cache._make_key("conv1", "query", None)
        key2 = cache._make_key("conv1", "query", None)
        assert key1 == key2

    def test_key_includes_analyst_role(self, cache: ResponseCache):
        """Test key includes analyst role."""
        key1 = cache._make_key("conv1", "query", "analyst1")
        key2 = cache._make_key("conv1", "query", "analyst2")
        assert key1 != key2

    def test_key_defaults_analyst_role(self, cache: ResponseCache):
        """Test key defaults analyst role to 'default'."""
        key1 = cache._make_key("conv1", "query", None)
        key2 = cache._make_key("conv1", "query", "default")
        assert key1 == key2

    def test_ttl_expiration(self, cache: ResponseCache):
        """Test TTL expiration."""
        response = {"text": "Hello"}
        cache.put("conv1", "query", response)
        
        # Manually expire by modifying cached_at
        key = cache._make_key("conv1", "query", None)
        resp, _ = cache._cache[key]
        expired_time = datetime.now(timezone.utc) - timedelta(seconds=1801)
        cache._cache[key] = (resp, expired_time)
        
        result = cache.get("conv1", "query", None)
        assert result is None  # Should be expired
        assert key not in cache._cache

    def test_lru_eviction(self, cache: ResponseCache):
        """Test LRU eviction when max_size exceeded."""
        # Fill cache to max_size
        for i in range(100):
            cache.put(f"conv{i}", f"query{i}", {"text": f"response{i}"})
        
        # Add one more - should evict oldest
        cache.put("conv100", "query100", {"text": "response100"})
        
        assert len(cache._cache) == 100
        # Oldest should be evicted
        result = cache.get("conv0", "query0", None)
        assert result is None  # Should be evicted

    def test_lru_order_preserved(self, cache: ResponseCache):
        """Test LRU order is preserved on access."""
        cache.put("conv1", "query1", {"text": "response1"})
        cache.put("conv2", "query2", {"text": "response2"})
        cache.put("conv3", "query3", {"text": "response3"})
        
        # Access conv1 - should move to end
        cache.get("conv1", "query1", None)
        
        # Add new entry - should evict conv2 (not conv1)
        cache.put("conv4", "query4", {"text": "response4"})
        
        assert cache.get("conv1", "query1", None) is not None
        assert cache.get("conv2", "query2", None) is None  # Evicted

    def test_put_overwrites_existing(self, cache: ResponseCache):
        """Test put overwrites existing entry."""
        cache.put("conv1", "query", {"text": "response1"})
        cache.put("conv1", "query", {"text": "response2"})
        
        result = cache.get("conv1", "query", None)
        assert result["text"] == "response2"  # Should be updated value

    def test_clear(self, cache: ResponseCache):
        """Test clear removes all entries."""
        cache.put("conv1", "query1", {"text": "response1"})
        cache.put("conv2", "query2", {"text": "response2"})
        
        cache.clear()
        assert len(cache._cache) == 0

    def test_cleanup_expired(self, cache: ResponseCache):
        """Test cleanup_expired removes expired entries."""
        # Add entries with different ages
        now = datetime.now(timezone.utc)
        key1 = cache._make_key("conv1", "query1", None)
        key2 = cache._make_key("conv2", "query2", None)
        
        cache._cache[key1] = ({"text": "response1"}, now - timedelta(seconds=1801))  # Expired
        cache._cache[key2] = ({"text": "response2"}, now - timedelta(seconds=900))  # Valid
        
        removed = cache.cleanup_expired()
        assert removed == 1
        assert key1 not in cache._cache
        assert key2 in cache._cache

    def test_stats(self, cache: ResponseCache):
        """Test stats calculation."""
        cache.put("conv1", "query", {"text": "response"})
        cache.get("conv1", "query", None)  # Hit
        cache.get("conv2", "missing", None)  # Miss
        
        stats = cache.stats()
        assert stats["hits"] == 1
        assert stats["misses"] == 1
        assert stats["size"] == 1
        assert stats["max_size"] == 100
        assert stats["hit_rate"] == 50.0  # 1 hit / 2 total = 50%

    def test_stats_zero_total(self, cache: ResponseCache):
        """Test stats with zero total requests."""
        stats = cache.stats()
        assert stats["hits"] == 0
        assert stats["misses"] == 0
        assert stats["hit_rate"] == 0.0

    def test_stats_counts_only_valid_entries(self, cache: ResponseCache):
        """Test stats counts only valid (non-expired) entries."""
        # Add expired entry
        now = datetime.now(timezone.utc)
        key = cache._make_key("conv1", "query1", None)
        cache._cache[key] = ({"text": "response1"}, now - timedelta(seconds=1801))
        
        # Add valid entry
        cache.put("conv2", "query2", {"text": "response2"})
        
        stats = cache.stats()
        assert stats["size"] == 1  # Only valid entry

    def test_different_analyst_roles(self, cache: ResponseCache):
        """Test different analyst roles create different cache entries."""
        cache.put("conv1", "query", {"text": "response1"}, analyst_role="analyst1")
        cache.put("conv1", "query", {"text": "response2"}, analyst_role="analyst2")
        
        assert cache.get("conv1", "query", "analyst1")["text"] == "response1"
        assert cache.get("conv1", "query", "analyst2")["text"] == "response2"

    def test_empty_conversation_id(self, cache: ResponseCache):
        """Test empty conversation ID."""
        cache.put("", "query", {"text": "response"})
        result = cache.get("", "query", None)
        assert result["text"] == "response"

    def test_empty_query(self, cache: ResponseCache):
        """Test empty query."""
        cache.put("conv1", "", {"text": "response"})
        result = cache.get("conv1", "", None)
        assert result["text"] == "response"

    def test_very_long_query(self, cache: ResponseCache):
        """Test very long query."""
        long_query = "a" * 10000
        cache.put("conv1", long_query, {"text": "response"})
        result = cache.get("conv1", long_query, None)
        assert result["text"] == "response"

    def test_unicode_conversation_id(self, cache: ResponseCache):
        """Test Unicode conversation ID."""
        cache.put("测试", "query", {"text": "response"})
        result = cache.get("测试", "query", None)
        assert result["text"] == "response"

    def test_complex_response_dict(self, cache: ResponseCache):
        """Test complex response dictionary."""
        complex_response = {
            "text": "Hello",
            "tokens": 10,
            "metadata": {"key": "value"},
            "choices": [{"text": "choice1"}, {"text": "choice2"}],
        }
        cache.put("conv1", "query", complex_response)
        result = cache.get("conv1", "query", None)
        assert result == complex_response

    def test_bug_key_collision(self, cache: ResponseCache):
        """BUG: Key collision may occur with hash collisions."""
        # SHA256 collisions are extremely rare but possible
        # BUG: Hash collisions may cause cache collisions
        # This test documents the potential issue
        pass

    def test_bug_ttl_check_may_have_race_condition(self, cache: ResponseCache):
        """BUG: TTL check may have race condition."""
        # Time may change between check and access
        # BUG: Race condition in TTL checking
        # This test documents the potential issue
        pass

    def test_bug_lru_eviction_may_not_work_correctly(self, cache: ResponseCache):
        """BUG: LRU eviction may not work correctly."""
        # OrderedDict operations may not preserve order correctly
        # BUG: LRU eviction may evict wrong entry
        # This test documents the potential issue
        pass

    def test_bug_stats_may_not_be_accurate(self, cache: ResponseCache):
        """BUG: Stats may not be accurate."""
        # Hit/miss counting may have race conditions
        # BUG: Stats accuracy may be affected by concurrency
        # This test documents the potential issue
        pass


class TestGetResponseCache:
    """Tests for get_response_cache global function."""

    def test_returns_singleton(self):
        """Test returns singleton instance."""
        from toolbox.cache.response_cache import get_response_cache
        
        cache1 = get_response_cache()
        cache2 = get_response_cache()
        assert cache1 is cache2

    def test_uses_environment_variables(self):
        """Test uses environment variables."""
        import os
        from toolbox.cache.response_cache import get_response_cache
        
        # Set environment variables
        os.environ["RESPONSE_CACHE_SIZE"] = "2000"
        os.environ["RESPONSE_CACHE_TTL_SECONDS"] = "3600"
        
        # Clear singleton to force recreation
        import toolbox.cache.response_cache as cache_module
        cache_module._response_cache = None
        
        cache = get_response_cache()
        assert cache.max_size == 2000
        assert cache.ttl_seconds == 3600

    def test_bug_singleton_may_not_be_thread_safe(self):
        """BUG: Singleton may not be thread-safe."""
        # Concurrent access may create multiple instances
        # BUG: Thread safety may not be guaranteed
        # This test documents the potential issue
        pass
