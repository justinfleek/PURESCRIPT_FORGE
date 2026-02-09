"""
Model Registry for Local TTS Provider.

Contains known models with their HuggingFace repos and SHA hashes.
Add new models here as they become available.
"""

from __future__ import annotations

from .types import TTSModelInfo


# NOTE: Update these SHAs when final model versions are released
# Use: sha256sum on downloaded model files to get actual SHA
MODELS_REGISTRY: dict[str, TTSModelInfo] = {
    "qwen3-tts-customvoice": TTSModelInfo(
        model_id="qwen3-tts-customvoice",
        hf_repo="Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice",
        model_name="Qwen3-TTS 1.7B CustomVoice",
        expected_sha="UPDATE_WITH_FINAL_SHA",  # TODO: Replace with actual SHA at launch
        requires_gpu=True,
        estimated_size_mb=3400,
    ),
    "qwen3-tts-voicedesign": TTSModelInfo(
        model_id="qwen3-tts-voicedesign",
        hf_repo="Qwen/Qwen3-TTS-12Hz-1.7B-VoiceDesign",
        model_name="Qwen3-TTS 1.7B VoiceDesign",
        expected_sha="UPDATE_WITH_FINAL_SHA",
        requires_gpu=True,
        estimated_size_mb=3400,
    ),
    "qwen3-tts-base": TTSModelInfo(
        model_id="qwen3-tts-base",
        hf_repo="Qwen/Qwen3-TTS-12Hz-1.7B-Base",
        model_name="Qwen3-TTS 1.7B Base",
        expected_sha="UPDATE_WITH_FINAL_SHA",
        requires_gpu=True,
        estimated_size_mb=3400,
    ),
}


__all__ = [
    "MODELS_REGISTRY",
]
