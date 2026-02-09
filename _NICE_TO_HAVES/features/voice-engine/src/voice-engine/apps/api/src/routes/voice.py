"""
Voice Chat API Routes

API endpoints for voice chat functionality:
- POST /voice/chat - Process voice input (audio), return transcript + AI response + audio
- GET /voice/models - List available TTS models
- POST /voice/models/download - Download/verify TTS model
"""

from fastapi import APIRouter, Depends, HTTPException, UploadFile
from typing_extensions import TypedDict

from toolbox.core import User
from toolbox.engines.voice.types import VoiceChatSession
from toolbox.engines.voice_chat import VoiceChatEngine

from ...deps import get_current_user, get_voice_chat_engine_service


# =============================================================================
# Response TypedDicts (explicit types for all returns)
# =============================================================================


class VoiceChatResponse(TypedDict):
    """Response from voice chat endpoint."""

    user_transcript: str
    stt_confidence: float
    stt_cost_usd: float
    assistant_text: str  # Text with thinking blocks stripped (for TTS)
    assistant_thinking: str | None  # Extracted thinking blocks (for UI)
    assistant_audio: bytes | None
    assistant_audio_format: str
    tts_cost_usd: float
    total_cost_usd: float
    stt_error: str | None
    chat_error: str | None
    tts_error: str | None


class TextChatResponse(TypedDict):
    """Response from text-only voice chat endpoint."""

    assistant_text: str  # Text with thinking blocks stripped (for TTS)
    assistant_thinking: str | None  # Extracted thinking blocks (for UI)
    assistant_audio_base64: str
    assistant_audio_format: str
    tts_cost_usd: float
    total_cost_usd: float
    chat_error: str | None
    tts_error: str | None


class TTSModelInfo(TypedDict):
    """TTS model information."""

    id: str
    name: str
    hf_repo: str
    status: str
    file_size_mb: float
    downloaded_at: str | None


class TTSModelsResponse(TypedDict):
    """Response listing available TTS models."""

    models: list[TTSModelInfo]


class ModelDownloadResponse(TypedDict):
    """Response from model download endpoint."""

    success: bool
    model_id: str
    status: str


class VoicesResponse(TypedDict):
    """Response listing available voices."""

    voices: list[str]


class EndSessionResponse(TypedDict):
    """Response from end session endpoint."""

    success: bool
    message: str


router = APIRouter(prefix="/voice", tags=["Voice"])


@router.post("/chat")
async def voice_chat(
    audio: UploadFile,
    conversation_id: str = "default",
    voice: str = "Ryan",
    language: str = "en",
    user: User = Depends(get_current_user),
    voice_chat: VoiceChatEngine = Depends(get_voice_chat_engine_service),
) -> VoiceChatResponse:
    """
    Process voice message end-to-end.

    1. Transcribe audio to text (STT)
    2. Get AI response (Chat)
    3. Synthesize response to audio (TTS)

    Returns:
        - user_transcript: Transcribed user speech
        - assistant_text: AI text response
        - assistant_audio_url: URL to AI audio (or base64)
        - cost_usd: Total cost of operation
        - errors: Any errors that occurred
    """
    try:
        # Read audio data
        audio_data = await audio.read()

        # Get audio format from filename
        audio_format = audio.filename.split(".")[-1] if audio.filename else "webm"

        # Process voice message
        result = await voice_chat.process_message(
            conversation_id=conversation_id,
            user_id=user.id,
            audio_data=audio_data,
            audio_format=audio_format,  # type: ignore
            language=language,
        )

        return {
            "user_transcript": result.get("user_transcript", ""),
            "stt_confidence": result.get("stt_confidence", 0.0),
            "stt_cost_usd": result.get("stt_cost_usd", 0.0),
            "assistant_text": result.get("assistant_text", ""),
            "assistant_thinking": result.get("assistant_thinking"),
            "assistant_audio": result.get("assistant_audio"),
            "assistant_audio_format": result.get("assistant_audio_format", "mp3"),
            "tts_cost_usd": result.get("tts_cost_usd", 0.0),
            "total_cost_usd": result.get("total_cost_usd", 0.0),
            "stt_error": result.get("stt_error"),
            "chat_error": result.get("chat_error"),
            "tts_error": result.get("tts_error"),
        }

    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Voice chat failed: {e!s}",
        )


@router.post("/chat/text")
async def voice_chat_text_only(
    text: str,
    conversation_id: str = "default",
    voice: str = "Ryan",
    user: User = Depends(get_current_user),
    voice_chat: VoiceChatEngine = Depends(get_voice_chat_engine_service),
) -> TextChatResponse:
    """
    Process text input and return audio output (TTS only).

    Useful for:
    - Testing TTS without microphone
    - Text input with audio response

    Returns:
        - assistant_text: AI text response
        - assistant_audio: AI audio bytes (base64 encoded)
        - cost_usd: Cost of operation
    """
    try:
        # Process text-only request
        result = await voice_chat.process_text_only(
            conversation_id=conversation_id,
            user_id=user.id,
            text=text,
        )

        # Encode audio as base64 for JSON response
        import base64

        audio_b64 = ""
        if result.get("assistant_audio"):
            audio_b64 = base64.b64encode(
                result["assistant_audio"]  # type: ignore
            ).decode("utf-8")

        return {
            "assistant_text": result.get("assistant_text", ""),
            "assistant_thinking": result.get("assistant_thinking"),
            "assistant_audio_base64": audio_b64,
            "assistant_audio_format": result.get("assistant_audio_format", "mp3"),
            "tts_cost_usd": result.get("tts_cost_usd", 0.0),
            "total_cost_usd": result.get("total_cost_usd", 0.0),
            "chat_error": result.get("chat_error"),
            "tts_error": result.get("tts_error"),
        }

    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Voice chat failed: {e!s}",
        )


@router.get("/models")
async def list_tts_models(
    user: User = Depends(get_current_user),
) -> TTSModelsResponse:
    """
    List available TTS models from registry.

    Returns:
        - models: List of model info (id, name, repo, status)
    """
    from ...deps import get_database_service

    database = get_database_service()
    
    # Get all TTS models from database
    rows = await database.fetch_all(
        "SELECT id, model_name, hf_repo, status, file_size_bytes, download_date FROM tts_models ORDER BY created_at ASC"
    )

    models: list[TTSModelInfo] = []
    for row in rows:
        # Extract and validate file_size_bytes
        file_size_bytes = row.get("file_size_bytes")
        file_size_mb: float = 0.0
        if isinstance(file_size_bytes, int | float):
            file_size_mb = float(file_size_bytes) / 1024 / 1024

        # Extract downloaded_at (could be str or None)
        downloaded_at_raw = row.get("download_date")
        downloaded_at: str | None = (
            str(downloaded_at_raw) if downloaded_at_raw is not None else None
        )

        models.append(
            TTSModelInfo(
                id=str(row.get("id", "")),
                name=str(row.get("model_name", "")),
                hf_repo=str(row.get("hf_repo", "")),
                status=str(row.get("status", "")),
                file_size_mb=file_size_mb,
                downloaded_at=downloaded_at,
            )
        )

    # Also include models from registry (not yet downloaded)
    from toolbox.engines.voice_local_provider import MODELS_REGISTRY

    existing_ids: set[str] = {m["id"] for m in models}
    for model_id, model_info in MODELS_REGISTRY.items():
        if model_id not in existing_ids:
            models.append(
                TTSModelInfo(
                    id=model_info["model_id"],
                    name=model_info["model_name"],
                    hf_repo=model_info["hf_repo"],
                    status="not_downloaded",
                    file_size_mb=float(model_info["estimated_size_mb"]) / 1024,
                    downloaded_at=None,
                )
            )

    return {"models": models}


@router.post("/models/download")
async def download_tts_model(
    model_id: str,
    user: User = Depends(get_current_user),
) -> ModelDownloadResponse:
    """
    Download and verify a TTS model from HuggingFace.

    Args:
        model_id: Model ID from MODELS_REGISTRY
        user: Current authenticated user

    Returns:
        - success: Whether download succeeded
        - status: Model status after operation
    """
    try:
        from toolbox.engines.voice_local_provider import LocalModelTTSProvider
        from ...deps import get_voice_engine_service

        voice_engine = get_voice_engine_service()
        tts_provider = voice_engine.tts_provider
        
        if isinstance(tts_provider, LocalModelTTSProvider):
            await tts_provider.ensure_model_downloaded()
            return ModelDownloadResponse(
                success=True,
                model_id=model_id,
                status="downloading",
            )

        raise HTTPException(
            status_code=400,
            detail="Download not supported for current TTS provider",
        )

    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Model download failed: {e!s}",
        ) from e


@router.get("/voices")
async def list_available_voices(
    user: User = Depends(get_current_user),
) -> VoicesResponse:
    """
    List available TTS voices (speakers).

    Returns:
        - voices: List of voice IDs and names
    """
    from ...deps import get_voice_engine_service

    voice_engine = get_voice_engine_service()
    voices = voice_engine.tts_provider.get_available_voices()

    return VoicesResponse(voices=voices)


@router.get("/sessions/{session_id}")
async def get_voice_session(
    session_id: str,
    user: User = Depends(get_current_user),
    voice_chat: VoiceChatEngine = Depends(get_voice_chat_engine_service),
) -> VoiceChatSession:
    """Get voice chat session by ID."""
    session = await voice_chat.get_session(session_id)

    if not session:
        raise HTTPException(
            status_code=404,
            detail=f"Voice chat session not found: {session_id}",
        )

    return session


@router.post("/sessions/{session_id}/end")
async def end_voice_session(
    session_id: str,
    user: User = Depends(get_current_user),
    voice_chat: VoiceChatEngine = Depends(get_voice_chat_engine_service),
) -> EndSessionResponse:
    """End a voice chat session."""
    await voice_chat.end_session(session_id)

    return EndSessionResponse(success=True, message="Voice chat session ended")
