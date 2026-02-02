"""
Memory Tests - Profiling and Leak Detection

Tests memory usage patterns:
- Memory leaks
- Peak memory usage
- Steady-state memory
- Cache memory footprint
"""

import asyncio
import gc
import tracemalloc
from typing import Callable

import pytest

from toolbox.engines.voice import VoiceEngine
from toolbox.cache import get_audio_cache, get_model_cache


class MemoryProfiler:
    """Memory profiling utilities."""
    
    @staticmethod
    def profile_function(func: Callable, *args, **kwargs) -> dict[str, int]:
        """Profile memory usage of a function."""
        tracemalloc.start()
        
        result = func(*args, **kwargs)
        if asyncio.iscoroutine(result):
            asyncio.run(result)
        
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        
        return {
            "current_bytes": current,
            "peak_bytes": peak,
        }
    
    @staticmethod
    def check_leak(func: Callable, iterations: int = 100) -> dict[str, int]:
        """Check for memory leaks by running function multiple times."""
        tracemalloc.start()
        
        for _ in range(iterations):
            result = func()
            if asyncio.iscoroutine(result):
                asyncio.run(result)
            gc.collect()
        
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        
        return {
            "current_bytes": current,
            "peak_bytes": peak,
            "iterations": iterations,
        }


@pytest.mark.asyncio
async def test_tts_memory_usage(voice_engine: VoiceEngine):
    """Test TTS memory usage."""
    profiler = MemoryProfiler()
    
    async def synthesize():
        return await voice_engine.text_to_speech(
            text="Hello, memory test",
            voice="test_voice",
        )
    
    memory = profiler.profile_function(synthesize)
    
    # Assert reasonable memory usage
    assert memory["peak_bytes"] < 50 * 1024 * 1024  # < 50MB
    
    print(f"\nTTS Memory:")
    print(f"  Peak: {memory['peak_bytes'] / 1024 / 1024:.2f} MB")


@pytest.mark.asyncio
async def test_cache_memory_footprint():
    """Test cache memory footprint."""
    audio_cache = get_audio_cache()
    audio_cache.clear()
    
    # Fill cache with many entries
    for i in range(1000):
        audio_cache.put(
            text=f"test text {i}",
            voice="test_voice",
            format="mp3",
            audio_bytes=b"mock_audio" * 1000,  # ~1KB per entry
        )
    
    tracemalloc.start()
    stats = audio_cache.stats()
    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    
    # Cache with 1000 entries should use reasonable memory
    assert peak < 10 * 1024 * 1024  # < 10MB for 1000 entries
    
    print(f"\nCache Memory:")
    print(f"  Entries: {stats['size']}")
    print(f"  Peak: {peak / 1024 / 1024:.2f} MB")


@pytest.mark.asyncio
async def test_memory_leak_detection(voice_engine: VoiceEngine):
    """Test for memory leaks in voice operations."""
    profiler = MemoryProfiler()
    
    async def synthesize():
        return await voice_engine.text_to_speech(
            text="Hello, leak test",
            voice="test_voice",
        )
    
    # Run many times and check memory doesn't grow unbounded
    memory = profiler.check_leak(synthesize, iterations=1000)
    
    # Memory should not grow linearly with iterations
    bytes_per_iteration = memory["peak_bytes"] / memory["iterations"]
    assert bytes_per_iteration < 1024 * 1024  # < 1MB per iteration
    
    print(f"\nMemory Leak Test:")
    print(f"  Iterations: {memory['iterations']}")
    print(f"  Peak: {memory['peak_bytes'] / 1024 / 1024:.2f} MB")
    print(f"  Bytes/iteration: {bytes_per_iteration:.2f}")


@pytest.mark.asyncio
async def test_model_cache_memory(model_cache):
    """Test model cache memory usage."""
    # Model cache should keep models in memory
    # This is expected behavior, but we should track it
    
    tracemalloc.start()
    
    # Simulate caching models
    for i in range(5):
        model_cache.put(f"model_{i}", object())
    
    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    
    stats = model_cache.stats()
    
    print(f"\nModel Cache Memory:")
    print(f"  Models cached: {stats['size']}")
    print(f"  Peak: {peak / 1024 / 1024:.2f} MB")


__all__ = []
