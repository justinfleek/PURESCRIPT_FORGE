"""
Test Data Fixtures - Reproducible Test Data

Provides reproducible test data generators for consistent testing.
"""

import random
from typing import Generator

import pytest


class TestDataGenerator:
    """Generates reproducible test data."""
    
    def __init__(self, seed: int = 42):
        """Initialize with seed."""
        self.rng = random.Random(seed)
    
    def generate_text(self, min_words: int = 5, max_words: int = 20) -> str:
        """Generate random text."""
        words = [
            "the", "quick", "brown", "fox", "jumps", "over", "lazy", "dog",
            "email", "marketing", "strategy", "content", "seo", "data",
            "analysis", "campaign", "audience", "performance", "optimization",
        ]
        num_words = self.rng.randint(min_words, max_words)
        return " ".join(self.rng.choices(words, k=num_words))
    
    def generate_audio_bytes(self, size_bytes: int = 1024) -> bytes:
        """Generate mock audio bytes."""
        return self.rng.randbytes(size_bytes)
    
    def generate_conversation_id(self) -> str:
        """Generate conversation ID."""
        return f"conv_{self.rng.randint(1000, 9999)}"
    
    def generate_user_id(self) -> str:
        """Generate user ID."""
        return f"user_{self.rng.randint(100, 999)}"


@pytest.fixture
def test_data_gen(reproducible_seed: int) -> TestDataGenerator:
    """Create test data generator."""
    return TestDataGenerator(seed=reproducible_seed)


@pytest.fixture
def sample_texts(test_data_gen: TestDataGenerator) -> list[str]:
    """Generate sample texts."""
    return [test_data_gen.generate_text() for _ in range(10)]


@pytest.fixture
def sample_audio_samples(test_data_gen: TestDataGenerator) -> list[bytes]:
    """Generate sample audio samples."""
    return [test_data_gen.generate_audio_bytes() for _ in range(10)]


__all__ = []
