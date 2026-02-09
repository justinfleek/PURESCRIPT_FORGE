"""
Deep comprehensive tests for AudioCache.

Tests caching, TTL, eviction, statistics, and bug detection.
"""
import pytest
from datetime import datetime, timezone, timedelta
from toolbox.cache.audio_cache import AudioCache


class TestAudioCache:
    """Deep comprehensive tests for AudioCache."""

    @pytest.fixture
    def cache(self):
        """Create AudioCache instance for testing."""
        return AudioCache(max_size=10, ttl_seconds=3600)

    def test_initialization(self, cache: AudioCache):
        """Test cache initialization."""
        assert cache.max_size == 10
        assert cache.ttl_seconds == 3600
        assert cache._hits == 0
        assert cache._misses == 0
        assert len(cache._cache) == 0

    def test_get_miss(self, cache: AudioCache):
        """Test get returns None on miss."""
        result = cache.get("test", "voice", "mp3")
        assert result is None
        assert cache._misses == 1
        assert cache._hits == 0

    def test_put_and_get(self, cache: AudioCache):
        """Test put and get operations."""
        audio_data = b"test audio data"
        cache.put("test", "voice", "mp3", audio_data)
        
        result = cache.get("test", "voice", "mp3")
        assert result == audio_data
        assert cache._hits == 1
        assert cache._misses == 0

    def test_key_generation_deterministic(self, cache: AudioCache):
        """Test key generation is deterministic."""
        key1 = cache._make_key("test", "voice", "mp3")
        key2 = cache._make_key("test", "voice", "mp3")
        assert key1 == key2

    def test_key_generation_different_inputs(self, cache: AudioCache):
        """Test key generation differs for different inputs."""
        key1 = cache._make_key("test1", "voice", "mp3")
        key2 = cache._make_key("test2", "voice", "mp3")
        assert key1 != key2

    def test_ttl_expiration(self, cache: AudioCache):
        """Test TTL expiration."""
        audio_data = b"test audio"
        cache.put("test", "voice", "mp3", audio_data)
        
        # Manually expire by modifying cached_at
        key = cache._make_key("test", "voice", "mp3")
        audio_bytes, _ = cache._cache[key]
        expired_time = datetime.now(timezone.utc) - timedelta(seconds=3601)
        cache._cache[key] = (audio_bytes, expired_time)
        
        result = cache.get("test", "voice", "mp3")
        assert result is None  # Should be expired
        assert key not in cache._cache

    def test_lru_eviction(self, cache: AudioCache):
        """Test LRU eviction when max_size exceeded."""
        # Fill cache to max_size
        for i in range(10):
            cache.put(f"text{i}", "voice", "mp3", b"audio")
        
        # Add one more - should evict oldest
        cache.put("text10", "voice", "mp3", b"audio")
        
        assert len(cache._cache) == 10
        # Oldest should be evicted
        result = cache.get("text0", "voice", "mp3")
        assert result is None  # Should be evicted

    def test_lru_order_preserved(self, cache: AudioCache):
        """Test LRU order is preserved on access."""
        cache.put("text1", "voice", "mp3", b"audio1")
        cache.put("text2", "voice", "mp3", b"audio2")
        cache.put("text3", "voice", "mp3", b"audio3")
        
        # Access text1 - should move to end
        cache.get("text1", "voice", "mp3")
        
        # Add new entry - should evict text2 (not text1)
        cache.put("text4", "voice", "mp3", b"audio4")
        
        assert cache.get("text1", "voice", "mp3") is not None
        assert cache.get("text2", "voice", "mp3") is None  # Evicted

    def test_put_overwrites_existing(self, cache: AudioCache):
        """Test put overwrites existing entry."""
        cache.put("test", "voice", "mp3", b"audio1")
        cache.put("test", "voice", "mp3", b"audio2")
        
        result = cache.get("test", "voice", "mp3")
        assert result == b"audio2"  # Should be updated value

    def test_clear(self, cache: AudioCache):
        """Test clear removes all entries."""
        cache.put("test1", "voice", "mp3", b"audio1")
        cache.put("test2", "voice", "mp3", b"audio2")
        
        cache.clear()
        assert len(cache._cache) == 0

    def test_cleanup_expired(self, cache: AudioCache):
        """Test cleanup_expired removes expired entries."""
        # Add entries with different ages
        now = datetime.now(timezone.utc)
        key1 = cache._make_key("test1", "voice", "mp3")
        key2 = cache._make_key("test2", "voice", "mp3")
        
        cache._cache[key1] = (b"audio1", now - timedelta(seconds=3601))  # Expired
        cache._cache[key2] = (b"audio2", now - timedelta(seconds=1800))  # Valid
        
        removed = cache.cleanup_expired()
        assert removed == 1
        assert key1 not in cache._cache
        assert key2 in cache._cache

    def test_stats(self, cache: AudioCache):
        """Test stats calculation."""
        cache.put("test", "voice", "mp3", b"audio")
        cache.get("test", "voice", "mp3")  # Hit
        cache.get("missing", "voice", "mp3")  # Miss
        
        stats = cache.stats()
        assert stats["hits"] == 1
        assert stats["misses"] == 1
        assert stats["size"] == 1
        assert stats["max_size"] == 10
        assert stats["hit_rate"] == 50.0  # 1 hit / 2 total = 50%

    def test_stats_zero_total(self, cache: AudioCache):
        """Test stats with zero total requests."""
        stats = cache.stats()
        assert stats["hits"] == 0
        assert stats["misses"] == 0
        assert stats["hit_rate"] == 0.0

    def test_unicode_text(self, cache: AudioCache):
        """Test Unicode text handling."""
        cache.put("测试", "voice", "mp3", b"audio")
        result = cache.get("测试", "voice", "mp3")
        assert result == b"audio"

    def test_empty_text(self, cache: AudioCache):
        """Test empty text."""
        cache.put("", "voice", "mp3", b"audio")
        result = cache.get("", "voice", "mp3")
        assert result == b"audio"

    def test_different_formats(self, cache: AudioCache):
        """Test different audio formats."""
        cache.put("test", "voice", "mp3", b"mp3_audio")
        cache.put("test", "voice", "wav", b"wav_audio")
        
        assert cache.get("test", "voice", "mp3") == b"mp3_audio"
        assert cache.get("test", "voice", "wav") == b"wav_audio"

    def test_different_voices(self, cache: AudioCache):
        """Test different voices."""
        cache.put("test", "voice1", "mp3", b"audio1")
        cache.put("test", "voice2", "mp3", b"audio2")
        
        assert cache.get("test", "voice1", "mp3") == b"audio1"
        assert cache.get("test", "voice2", "mp3") == b"audio2"

    def test_very_long_text(self, cache: AudioCache):
        """Test very long text."""
        long_text = "a" * 10000
        cache.put(long_text, "voice", "mp3", b"audio")
        result = cache.get(long_text, "voice", "mp3")
        assert result == b"audio"

    def test_empty_audio_bytes(self, cache: AudioCache):
        """Test empty audio bytes."""
        cache.put("test", "voice", "mp3", b"")
        result = cache.get("test", "voice", "mp3")
        assert result == b""

    def test_very_large_audio_bytes(self, cache: AudioCache):
        """Test very large audio bytes."""
        large_audio = b"x" * (10 * 1024 * 1024)  # 10MB
        cache.put("test", "voice", "mp3", large_audio)
        result = cache.get("test", "voice", "mp3")
        assert result == large_audio

    def test_bug_key_collision(self, cache: AudioCache):
        """BUG: Key collision may occur with hash collisions."""
        # SHA256 collisions are extremely rare but possible
        # BUG: Hash collisions may cause cache collisions
        # This test documents the potential issue
        pass

    def test_bug_ttl_check_may_have_race_condition(self, cache: AudioCache):
        """BUG: TTL check may have race condition."""
        # Time may change between check and access
        # BUG: Race condition in TTL checking
        # This test documents the potential issue
        pass

    def test_bug_lru_eviction_may_not_work_correctly(self, cache: AudioCache):
        """BUG: LRU eviction may not work correctly."""
        # OrderedDict operations may not preserve order correctly
        # BUG: LRU eviction may evict wrong entry
        # This test documents the potential issue
        pass

    def test_bug_stats_may_not_be_accurate(self, cache: AudioCache):
        """BUG: Stats may not be accurate."""
        # Hit/miss counting may have race conditions
        # BUG: Stats accuracy may be affected by concurrency
        # This test documents the potential issue
        pass


class TestGetAudioCache:
    """Tests for get_audio_cache global function."""

    def test_returns_singleton(self):
        """Test returns singleton instance."""
        from toolbox.cache.audio_cache import get_audio_cache
        
        cache1 = get_audio_cache()
        cache2 = get_audio_cache()
        assert cache1 is cache2

    def test_uses_environment_variables(self):
        """Test uses environment variables."""
        import os
        from toolbox.cache.audio_cache import get_audio_cache
        
        # Set environment variables
        os.environ["AUDIO_CACHE_SIZE"] = "500"
        os.environ["AUDIO_CACHE_TTL_SECONDS"] = "7200"
        
        # Clear singleton to force recreation
        import toolbox.cache.audio_cache as cache_module
        cache_module._audio_cache = None
        
        cache = get_audio_cache()
        assert cache.max_size == 500
        assert cache.ttl_seconds == 7200

    def test_bug_singleton_may_not_be_thread_safe(self):
        """BUG: Singleton may not be thread-safe."""
        # Concurrent access may create multiple instances
        # BUG: Thread safety may not be guaranteed
        # This test documents the potential issue
        pass
