"""
Local Model TTS Provider - HuggingFace-based model management.

Downloads and manages local TTS models from HuggingFace:
- Qwen3-TTS models (CustomVoice, VoiceDesign, Base)
- Version control via SHA hashes
- Database integration for model tracking
- Future-proof design for any HF model

Usage:
    provider = LocalModelTTSProvider(
        db=db,
        model_id="qwen3-tts-customvoice",
        hf_repo="Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice",
        expected_sha="abc123...",
    )

    # Ensure model is downloaded
    await provider.ensure_model_downloaded()

    # Synthesize speech
    audio = await provider.synthesize(text="Hello world")
"""

from __future__ import annotations

import logging
from pathlib import Path

from .registry import MODELS_REGISTRY
from .types import TTSModelInfo, VoiceDatabaseProtocol
from .utils import calculate_model_sha, wav_to_mp3


logger = logging.getLogger(__name__)


class LocalModelTTSProvider:
    """
    Local model TTS provider using HuggingFace models.

    Downloads and manages models from HuggingFace, stores metadata in database.
    Loads qwen-tts library for inference.

    Future-proof: Can support any HF model by adding to MODELS_REGISTRY.
    """

    def __init__(
        self,
        db: VoiceDatabaseProtocol,
        model_id: str,
        hf_repo: str | None = None,
        expected_sha: str | None = None,
        models_dir: str | Path | None = None,
        device: str = "cuda:0",
    ) -> None:
        """
        Initialize local model TTS provider.

        Args:
            db: Database connection (implements VoiceDatabaseProtocol)
            model_id: Model ID from MODELS_REGISTRY
            hf_repo: Override HuggingFace repo (uses registry if None)
            expected_sha: Override expected SHA (uses registry if None)
            models_dir: Directory to store models (default: ./models/tts/)
            device: Torch device for inference
        """
        self.db: VoiceDatabaseProtocol = db
        self.model_id = model_id
        self.device = device

        # Get model info from registry or use overrides
        if model_id in MODELS_REGISTRY:
            # Copy to avoid mutating the global registry
            self._model_info: TTSModelInfo = TTSModelInfo(
                model_id=MODELS_REGISTRY[model_id]["model_id"],
                hf_repo=hf_repo or MODELS_REGISTRY[model_id]["hf_repo"],
                model_name=MODELS_REGISTRY[model_id]["model_name"],
                expected_sha=expected_sha or MODELS_REGISTRY[model_id]["expected_sha"],
                requires_gpu=MODELS_REGISTRY[model_id]["requires_gpu"],
                estimated_size_mb=MODELS_REGISTRY[model_id]["estimated_size_mb"],
            )
        else:
            # Custom model
            self._model_info = TTSModelInfo(
                model_id=model_id,
                hf_repo=hf_repo or "",
                model_name=model_id,
                expected_sha=expected_sha or "",
                requires_gpu=True,
                estimated_size_mb=0,
            )

        # Models directory
        if models_dir is None:
            models_dir = Path(__file__).parent.parent.parent.parent / "models" / "tts"
        self.models_dir = Path(models_dir)
        self.models_dir.mkdir(parents=True, exist_ok=True)

        # Loaded model instance (typed as object since we lazy-import the model class)
        self._model: object | None = None
        self._tokenizer: object | None = None

    # ========================================================================
    # TTSProviderProtocol Implementation
    # ========================================================================

    async def synthesize(
        self,
        text: str,
        voice: str = "Ryan",  # Qwen default speaker
        model: str | None = None,  # Ignored - uses internal model
        speed: float = 1.0,
        format: str = "mp3",
    ) -> bytes:
        """
        Synthesize speech using local Qwen3-TTS model.

        Args:
            text: Text to synthesize
            voice: Speaker name (Qwen: Ryan, Vivian, etc.)
            model: Ignored (uses loaded model)
            speed: Speed multiplier (Qwen doesn't support this)
            format: Audio format

        Returns:
            Raw audio bytes (MP3 or WAV)

        Raises:
            RuntimeError: If model not loaded or synthesis fails
        """
        # Ensure model is loaded
        if self._model is None:
            await self._ensure_model_loaded()

        # Validate text
        if not text:
            raise ValueError("Text cannot be empty")

        # Model must be loaded after _ensure_model_loaded
        if self._model is None:
            raise RuntimeError("Model failed to load")

        # Check audio cache first
        from toolbox.cache import get_audio_cache
        audio_cache = get_audio_cache()
        cached_audio = audio_cache.get(text, voice, format)
        
        if cached_audio is not None:
            logger.debug(f"Audio cache HIT for text: {text[:50]}...")
            return cached_audio
        
        # Generate audio using qwen-tts
        import io

        try:
            import soundfile as sf  # type: ignore[import-not-found]

            # Generate with qwen-tts (model has generate_custom_voice method)
            generate_fn = self._model.generate_custom_voice
            wavs, sr = generate_fn(
                text=text,
                language="Auto",  # Auto-detect
                speaker=voice,
            )

            # Convert numpy array to WAV
            buffer = io.BytesIO()
            sf.write(buffer, wavs[0], sr, format="WAV")
            wav_bytes = buffer.getvalue()

            # Convert to MP3 if requested
            if format == "mp3":
                audio_bytes = wav_to_mp3(wav_bytes)
            else:
                audio_bytes = wav_bytes
            
            # Cache the result
            audio_cache.put(text, voice, format, audio_bytes)
            logger.debug(f"Generated and cached audio for text: {text[:50]}...")
            
            return audio_bytes

        except ImportError as e:
            raise RuntimeError(f"Required dependencies not installed: {e}") from e
        except Exception as e:
            logger.error(f"TTS synthesis failed: {e}")
            raise RuntimeError(f"Synthesis failed: {e}") from e

    def get_available_voices(self) -> list[str]:
        """Get list of available Qwen speakers."""
        # Qwen3-TTS CustomVoice has 9 preset speakers
        return [
            "Ryan",
            "Vivian",
            "Sophia",
            "Alex",
            "Emma",
            "James",
            "Maria",
            "David",
            "Luna",
        ]

    def estimate_cost(self, text: str, model: str | None = None) -> float:
        """
        Estimate cost (always 0 for local models).

        Args:
            text: Text to synthesize
            model: Model ID (ignored)

        Returns:
            0.0 (local models are free)
        """
        return 0.0

    # ========================================================================
    # Model Management
    # ========================================================================

    async def ensure_model_downloaded(self) -> bool:
        """
        Ensure model is downloaded and ready.

        Downloads from HuggingFace if needed.
        Verifies SHA hash after download.

        Returns:
            True if model is ready, False otherwise

        Raises:
            RuntimeError: If download fails or SHA mismatch
        """
        # Check if model is already in database
        model_row = await self._get_model_record()

        if model_row:
            status = model_row.get("status")
            if status == "ready":
                local_path = model_row.get("local_path")
                if isinstance(local_path, str) and Path(local_path).exists():
                    return True

            # Check for SHA mismatch
            if status == "mismatch":
                logger.warning(f"Model SHA mismatch, re-downloading: {self.model_id}")
                await self._download_model()

            return False

        # Model not in database, download it
        await self._download_model()
        return True

    async def _ensure_model_loaded(self) -> None:
        """Ensure Qwen3-TTS model is loaded in memory."""
        if self._model is not None:
            return

        # Ensure model is downloaded
        await self.ensure_model_downloaded()

        # Get model path
        model_row = await self._get_model_record()
        if not model_row:
            raise RuntimeError(f"Model record not found: {self.model_id}")

        local_path = model_row.get("local_path")
        if not isinstance(local_path, str):
            raise RuntimeError(f"Model path not set: {self.model_id}")

        model_path = Path(local_path)
        if not model_path.exists():
            raise RuntimeError(f"Model path doesn't exist: {model_path}")

        # Load qwen-tts model
        try:
            import torch  # type: ignore[import-not-found]
            import sys
            from pathlib import Path
            
            # Add Qwen3-TTS source to path if not installed as package
            qwen_source = Path(__file__).parent.parent.parent.parent.parent.parent / "Qwen3-TTS-main"
            if qwen_source.exists() and str(qwen_source) not in sys.path:
                sys.path.insert(0, str(qwen_source))
            
            from qwen_tts import Qwen3TTSModel  # type: ignore[import-not-found]

            self._model = Qwen3TTSModel.from_pretrained(
                str(model_path),
                device_map=self.device,
                dtype=torch.bfloat16,
            )

            logger.info(f"Loaded Qwen3-TTS model: {self.model_id}")

        except ImportError:
            raise RuntimeError("qwen-tts not installed. Install with: pip install qwen-tts")
        except Exception as e:
            logger.error(f"Failed to load model: {e}")
            raise RuntimeError(f"Failed to load model: {e}") from e

    async def _download_model(self) -> None:
        """
        Download model from HuggingFace.

        Uses huggingface_hub library.
        Verifies SHA after download.
        """
        from datetime import timezone, datetime

        hf_repo = self._model_info["hf_repo"]
        model_dir = self.models_dir / self.model_id

        # Update database status
        await self._update_model_status("downloading")

        try:
            # Download using huggingface_hub
            try:
                from huggingface_hub import snapshot_download  # type: ignore[import-not-found]
            except ImportError:
                raise RuntimeError(
                    "huggingface_hub not installed. Install with: pip install huggingface_hub"
                )

            logger.info(f"Downloading model: {hf_repo}")

            snapshot_download(
                repo_id=hf_repo,
                local_dir=str(model_dir),
                local_dir_use_symlinks=False,
            )

            # Calculate SHA of downloaded files
            actual_sha = await calculate_model_sha(model_dir)

            # Verify SHA
            expected_sha = self._model_info["expected_sha"]
            if expected_sha != "UPDATE_WITH_FINAL_SHA" and actual_sha != expected_sha:
                await self._update_model_status(
                    "mismatch",
                    actual_sha=actual_sha,
                    error_message=f"SHA mismatch: expected {expected_sha}, got {actual_sha}",
                )
                raise RuntimeError(f"Model SHA verification failed for {self.model_id}")

            # Calculate file size
            total_size = sum(f.stat().st_size for f in model_dir.rglob("*") if f.is_file())

            # Update database as ready
            now = datetime.now(timezone.utc).isoformat()
            await self.db.execute(
                """
                INSERT OR REPLACE INTO tts_models
                (id, hf_repo, model_name, expected_sha, actual_sha,
                 local_path, status, file_size_bytes, download_date,
                 last_verified_date, created_at, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    self.model_id,
                    hf_repo,
                    self._model_info["model_name"],
                    expected_sha,
                    actual_sha,
                    str(model_dir),
                    "ready",
                    total_size,
                    now,
                    now,
                    now,
                    now,
                ),
            )

            logger.info(f"Model downloaded and verified: {self.model_id}")

        except Exception as e:
            logger.error(f"Failed to download model: {e}")
            await self._update_model_status(
                "error",
                error_message=str(e),
            )
            raise RuntimeError(f"Failed to download model {self.model_id}: {e}") from e

    # ========================================================================
    # Database Operations
    # ========================================================================

    async def _get_model_record(self):
        """Get model record from database."""
        query = """
        SELECT id, hf_repo, model_name, expected_sha, actual_sha,
               local_path, status, file_size_bytes, download_date,
               last_verified_date, error_message, created_at, updated_at
        FROM tts_models
        WHERE id = ?
        """

        return await self.db.fetch_one(query, (self.model_id,))

    async def _update_model_status(
        self,
        status: str,
        actual_sha: str | None = None,
        error_message: str | None = None,
    ) -> None:
        """Update model status in database."""
        from datetime import timezone, datetime

        now = datetime.now(timezone.utc).isoformat()

        await self.db.execute(
            """
            INSERT OR REPLACE INTO tts_models
            (id, hf_repo, model_name, expected_sha, actual_sha,
             local_path, status, error_message, created_at, updated_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                self.model_id,
                self._model_info["hf_repo"],
                self._model_info["model_name"],
                self._model_info["expected_sha"],
                actual_sha,
                None,  # local_path set after download
                status,
                error_message,
                now,
                now,
            ),
        )


# =============================================================================
# Factory
# =============================================================================


def create_local_model_tts_provider(
    db: VoiceDatabaseProtocol,
    model_id: str,
    hf_repo: str | None = None,
    expected_sha: str | None = None,
    models_dir: str | Path | None = None,
    device: str = "cuda:0",
) -> LocalModelTTSProvider:
    """
    Factory function to create local model TTS provider.

    Args:
        db: Database connection
        model_id: Model ID (e.g., "qwen3-tts-customvoice")
        hf_repo: Override HuggingFace repo
        expected_sha: Override expected SHA
        models_dir: Directory for models
        device: Torch device

    Returns:
        LocalModelTTSProvider instance
    """
    return LocalModelTTSProvider(
        db=db,
        model_id=model_id,
        hf_repo=hf_repo,
        expected_sha=expected_sha,
        models_dir=models_dir,
        device=device,
    )


# =============================================================================
# Initialization
# =============================================================================


async def init_tts_models_table(db: VoiceDatabaseProtocol) -> None:
    """Initialize TTS models table."""
    from .types import MODELS_TABLE

    await db.execute(MODELS_TABLE)


__all__ = [
    "LocalModelTTSProvider",
    "create_local_model_tts_provider",
    "init_tts_models_table",
]
