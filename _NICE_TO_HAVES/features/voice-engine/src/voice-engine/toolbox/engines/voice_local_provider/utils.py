"""
Utility functions for Local Model TTS Provider.

Contains:
- Audio format conversion (WAV to MP3)
- Model SHA calculation
"""

from __future__ import annotations

import hashlib
import logging
from pathlib import Path


logger = logging.getLogger(__name__)


def wav_to_mp3(wav_bytes: bytes) -> bytes:
    """Convert WAV bytes to MP3.

    Args:
        wav_bytes: Raw WAV audio data

    Returns:
        MP3 audio data, or original WAV if conversion fails
    """
    try:
        import io

        import pydub  # type: ignore[import-not-found]

        # Load WAV
        wav_audio = pydub.AudioSegment.from_file(io.BytesIO(wav_bytes), format="wav")

        # Export as MP3
        mp3_buffer = io.BytesIO()
        wav_audio.export(mp3_buffer, format="mp3", bitrate="128k")

        return mp3_buffer.getvalue()

    except ImportError:
        logger.warning("pydub not installed, returning WAV")
        return wav_bytes
    except Exception as e:
        logger.error(f"Failed to convert WAV to MP3: {e}")
        return wav_bytes


async def calculate_model_sha(model_dir: Path) -> str:
    """Calculate SHA256 of all files in model directory.

    Args:
        model_dir: Path to model directory

    Returns:
        SHA256 hex digest of all files combined
    """
    import asyncio

    sha_hash = hashlib.sha256()

    # Calculate SHA of all files
    for file_path in sorted(model_dir.rglob("*")):
        if file_path.is_file():
            # Run in thread to avoid blocking
            def calc_hash(f: Path) -> None:
                sha_hash.update(f.read_bytes())

            await asyncio.to_thread(calc_hash, file_path)

    return sha_hash.hexdigest()


__all__ = [
    "wav_to_mp3",
    "calculate_model_sha",
]
