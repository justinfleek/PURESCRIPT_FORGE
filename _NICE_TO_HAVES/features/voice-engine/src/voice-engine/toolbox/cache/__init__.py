"""
Caching Layer - Model, Audio, and Response Caching

Provides caching for:
- TTS model instances (avoid reloading)
- Audio synthesis results (cache by text+voice)
- Chat responses (cache by conversation+query)
- STT results (cache by audio hash)

Caching strategies:
- LRU for memory-bound caches
- TTL for time-bound caches
- Size-based eviction for disk caches
"""

from .model_cache import ModelCache, get_model_cache
from .audio_cache import AudioCache, get_audio_cache
from .response_cache import ResponseCache, get_response_cache

__all__ = [
    "ModelCache",
    "get_model_cache",
    "AudioCache",
    "get_audio_cache",
    "ResponseCache",
    "get_response_cache",
]
