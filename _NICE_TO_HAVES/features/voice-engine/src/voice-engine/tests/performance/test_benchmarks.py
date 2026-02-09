"""
Performance Tests - Benchmarking

Measures performance characteristics:
- Latency (p50, p95, p99)
- Throughput (requests/second)
- Memory usage (peak, steady-state)
- Cache hit rates
"""

import asyncio
import time
import tracemalloc
from statistics import mean, median, stdev

import pytest

from toolbox.engines.voice import VoiceEngine
from toolbox.cache import get_audio_cache, get_response_cache


class PerformanceBenchmark:
    """Performance benchmarking utilities."""
    
    @staticmethod
    def measure_latency(func, *args, **kwargs) -> dict[str, float]:
        """Measure function latency."""
        times = []
        for _ in range(100):
            start = time.perf_counter()
            result = func(*args, **kwargs)
            if asyncio.iscoroutine(result):
                asyncio.run(result)
            end = time.perf_counter()
            times.append((end - start) * 1000)  # Convert to ms
        
        times.sort()
        return {
            "p50": median(times),
            "p95": times[int(len(times) * 0.95)],
            "p99": times[int(len(times) * 0.99)],
            "mean": mean(times),
            "std": stdev(times) if len(times) > 1 else 0.0,
            "min": min(times),
            "max": max(times),
        }
    
    @staticmethod
    def measure_memory(func, *args, **kwargs) -> dict[str, int]:
        """Measure function memory usage."""
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


@pytest.mark.asyncio
async def test_tts_latency(voice_engine: VoiceEngine):
    """Benchmark TTS synthesis latency."""
    benchmark = PerformanceBenchmark()
    
    async def synthesize():
        return await voice_engine.text_to_speech(
            text="Hello, this is a performance test",
            voice="test_voice",
        )
    
    stats = benchmark.measure_latency(synthesize)
    
    # Assert reasonable performance
    assert stats["p95"] < 1000.0  # p95 < 1 second
    assert stats["mean"] < 500.0  # Mean < 500ms
    
    print(f"\nTTS Latency (ms):")
    print(f"  Mean: {stats['mean']:.2f}")
    print(f"  P50: {stats['p50']:.2f}")
    print(f"  P95: {stats['p95']:.2f}")
    print(f"  P99: {stats['p99']:.2f}")


@pytest.mark.asyncio
async def test_stt_latency(voice_engine: VoiceEngine, sample_audio_bytes: bytes):
    """Benchmark STT transcription latency."""
    benchmark = PerformanceBenchmark()
    
    async def transcribe():
        return await voice_engine.speech_to_text(
            audio_data=sample_audio_bytes,
            audio_format="wav",
            language="en",
        )
    
    stats = benchmark.measure_latency(transcribe)
    
    # Assert reasonable performance
    assert stats["p95"] < 2000.0  # p95 < 2 seconds
    
    print(f"\nSTT Latency (ms):")
    print(f"  Mean: {stats['mean']:.2f}")
    print(f"  P50: {stats['p50']:.2f}")
    print(f"  P95: {stats['p95']:.2f}")


@pytest.mark.asyncio
async def test_routing_performance():
    """Benchmark routing performance."""
    from toolbox.llm.routing import route_query
    
    benchmark = PerformanceBenchmark()
    
    queries = [
        "email marketing strategy",
        "SEO optimization tips",
        "content calendar planning",
        "data analysis report",
    ]
    
    def route():
        for query in queries:
            route_query(query)
    
    stats = benchmark.measure_latency(route)
    
    # Routing should be very fast
    assert stats["mean"] < 10.0  # Mean < 10ms
    
    print(f"\nRouting Latency (ms):")
    print(f"  Mean: {stats['mean']:.4f}")
    print(f"  P95: {stats['p95']:.4f}")


@pytest.mark.asyncio
async def test_cache_performance():
    """Benchmark cache performance."""
    audio_cache = get_audio_cache()
    audio_cache.clear()
    
    # Fill cache
    for i in range(100):
        audio_cache.put(
            text=f"test text {i}",
            voice="test_voice",
            format="mp3",
            audio_bytes=b"mock_audio_data" * 100,
        )
    
    # Measure cache hit latency
    benchmark = PerformanceBenchmark()
    
    def cache_get():
        audio_cache.get("test text 50", "test_voice", "mp3")
    
    stats = benchmark.measure_latency(cache_get)
    
    # Cache should be very fast
    assert stats["mean"] < 1.0  # Mean < 1ms
    
    cache_stats = audio_cache.stats()
    assert cache_stats["hit_rate"] > 0.0
    
    print(f"\nCache Latency (ms):")
    print(f"  Mean: {stats['mean']:.4f}")
    print(f"  Hit Rate: {cache_stats['hit_rate']:.2f}%")


@pytest.mark.asyncio
async def test_memory_usage(voice_engine: VoiceEngine):
    """Measure memory usage of voice operations."""
    benchmark = PerformanceBenchmark()
    
    async def synthesize():
        return await voice_engine.text_to_speech(
            text="Hello, memory test",
            voice="test_voice",
        )
    
    memory = benchmark.measure_memory(synthesize)
    
    # Assert reasonable memory usage
    assert memory["peak_bytes"] < 100 * 1024 * 1024  # < 100MB
    
    print(f"\nMemory Usage:")
    print(f"  Current: {memory['current_bytes'] / 1024 / 1024:.2f} MB")
    print(f"  Peak: {memory['peak_bytes'] / 1024 / 1024:.2f} MB")


__all__ = []
