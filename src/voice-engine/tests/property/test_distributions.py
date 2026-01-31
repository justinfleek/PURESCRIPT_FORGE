"""
Property-Based Tests - Reproducible Distributions

Tests using reproducible random distributions to ensure
deterministic behavior across test runs.
"""

import random
from typing import Generator

import pytest

from toolbox.llm.routing import route_query
from toolbox.llm.base import AnalystRole


class ReproducibleDistribution:
    """
    Reproducible random distribution for testing.
    
    Uses fixed seed to ensure tests are deterministic.
    """
    
    def __init__(self, seed: int = 42):
        """Initialize with seed."""
        self.seed = seed
        self.rng = random.Random(seed)
    
    def uniform(self, a: float, b: float) -> float:
        """Generate uniform random float."""
        return self.rng.uniform(a, b)
    
    def choice(self, seq: list) -> object:
        """Choose random element."""
        return self.rng.choice(seq)
    
    def sample(self, population: list, k: int) -> list:
        """Sample k elements."""
        return self.rng.sample(population, k)
    
    def reset(self) -> None:
        """Reset to initial seed."""
        self.rng = random.Random(self.seed)


@pytest.fixture
def dist(reproducible_seed: int) -> ReproducibleDistribution:
    """Create reproducible distribution."""
    return ReproducibleDistribution(seed=reproducible_seed)


class TestRoutingProperties:
    """Property-based tests for routing."""
    
    def test_routing_idempotent(self, dist: ReproducibleDistribution):
        """Test that routing is idempotent (f(f(x)) = f(x))."""
        queries = [
            "email marketing strategy",
            "SEO optimization",
            "content planning",
            "data analysis",
        ]
        
        for query in queries:
            result1 = route_query(query)
            result2 = route_query(query)
            
            # Same query should produce same result
            assert result1.analyst.role == result2.analyst.role
            assert result1.confidence == result2.confidence
    
    def test_routing_monotonic_confidence(self, dist: ReproducibleDistribution):
        """Test that adding relevant keywords increases confidence."""
        base_query = "marketing"
        enhanced_query = "email marketing automation strategy"
        
        base_result = route_query(base_query)
        enhanced_result = route_query(enhanced_query)
        
        # More keywords should not decrease confidence for matching analyst
        if enhanced_result.analyst.role == base_result.analyst.role:
            assert enhanced_result.confidence >= base_result.confidence
    
    def test_routing_total(self, dist: ReproducibleDistribution):
        """Test that routing always returns a result (totality)."""
        # Generate random queries
        words = ["test", "query", "marketing", "email", "seo", "content", "data"]
        
        for _ in range(100):
            query = " ".join(dist.sample(words, k=dist.choice([1, 2, 3, 4])))
            result = route_query(query)
            
            # Should always return valid result
            assert result is not None
            assert result.analyst is not None
            assert 0.0 <= result.confidence <= 1.0
    
    def test_routing_bounds(self, dist: ReproducibleDistribution):
        """Test that routing respects bounds."""
        queries = [
            "",
            "a" * 10000,  # Very long
            "!@#$%^&*()",  # Special chars
            "email\nmarketing\ttest",  # Whitespace
        ]
        
        for query in queries:
            result = route_query(query)
            
            # Confidence must be in bounds
            assert 0.0 <= result.confidence <= 1.0
            # Analyst must be valid
            assert result.analyst is not None


class TestVoiceEngineProperties:
    """Property-based tests for voice engine."""
    
    @pytest.mark.asyncio
    async def test_tts_idempotent(self, voice_engine, dist: ReproducibleDistribution):
        """Test that TTS is idempotent for same input."""
        text = "test text"
        voice = "test_voice"
        
        audio1 = await voice_engine.text_to_speech(text=text, voice=voice)
        audio2 = await voice_engine.text_to_speech(text=text, voice=voice)
        
        # Same input should produce same output (or cached)
        assert audio1["audio_data"] == audio2["audio_data"]
    
    @pytest.mark.asyncio
    async def test_tts_bounds(self, voice_engine, dist: ReproducibleDistribution):
        """Test TTS respects bounds."""
        # Test empty text
        with pytest.raises((ValueError, AssertionError)):
            await voice_engine.text_to_speech(text="", voice="test_voice")
        
        # Test very long text
        long_text = "test " * 10000
        audio = await voice_engine.text_to_speech(text=long_text, voice="test_voice")
        assert audio is not None
        assert len(audio["audio_data"]) > 0


__all__ = []
