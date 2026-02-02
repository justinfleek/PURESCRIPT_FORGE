"""
Voice Chat Engine - Integrates ChatEngine and VoiceEngine

Combines text chat with voice capabilities for full voice chat experience.

Features:
- Process voice input (audio -> text via STT)
- Get AI response (text chat via ChatEngine)
- Synthesize voice output (text -> audio via TTS)
- Manage voice chat sessions
- Track voice usage and costs

Usage:
    voice_engine = VoiceEngine(db=db, tts_provider=tts, stt_provider=stt)
    chat_engine = ChatEngine(db=db)

    voice_chat = VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )

    # Process voice message
    result = await voice_chat.process_message(
        conversation_id="conv_123",
        user_id="user_456",
        audio_data=audio_bytes,
    )

    # Returns: {
    #   "user_transcript": "Hello world",
    #   "assistant_text": "Hi! How can I help?",
    #   "assistant_audio": b"...",
    #   "voice_message": VoiceChatMessage,
    #   "cost_usd": 0.015
    # }
"""

from __future__ import annotations

import logging
from typing import TYPE_CHECKING, Literal

from typing_extensions import TypedDict

from toolbox.llm.chat_template import extract_thinking, strip_thinking


if TYPE_CHECKING:
    from toolbox.engines.chatbot.venice_chat import VeniceChatEngine as ChatEngine
    from toolbox.engines.voice import (
        TTSResponse,
        VoiceChatConfig,
        VoiceChatMessage,
        VoiceChatSession,
        VoiceEngine,
    )
    from toolbox.orchestration import MaestroOrchestrator

logger = logging.getLogger(__name__)


# =============================================================================
# Result Types
# =============================================================================


class VoiceChatResult(TypedDict):
    """Result of processing a voice message."""

    # User input
    user_transcript: str
    stt_confidence: float
    stt_cost_usd: float

    # Assistant response
    assistant_text: str  # Text with thinking blocks stripped (for TTS)
    assistant_thinking: str | None  # Extracted thinking blocks (for UI)
    assistant_audio: bytes | None
    assistant_audio_format: str
    tts_cost_usd: float

    # Voice session tracking
    voice_message: VoiceChatMessage | None

    # Total cost
    total_cost_usd: float

    # Errors
    stt_error: str | None
    chat_error: str | None
    tts_error: str | None


# =============================================================================
# Voice Chat Engine
# =============================================================================


class VoiceChatEngine:
    """
    Voice chat engine with MAESTRO integration for intelligent agent routing.
    Voice chat engine that integrates text chat with voice capabilities.

    Zero internal FORGE dependencies - only stdlib + typing.
    Uses protocols for ChatEngine and VoiceEngine.
    """

    def __init__(
        self,
        chat_engine: ChatEngine,
        voice_engine: VoiceEngine,
        maestro: MaestroOrchestrator | None = None,
    ) -> None:
        """
        Initialize voice chat engine.

        Args:
            chat_engine: Chat engine for text chat
            voice_engine: Voice engine for TTS/STT
            maestro: Optional MAESTRO orchestrator for agent routing
        """
        self.chat_engine = chat_engine
        self.voice_engine = voice_engine
        self.maestro = maestro

    async def create_session(
        self,
        conversation_id: str,
        org_id: str,
        user_id: str,
        config: VoiceChatConfig | None = None,
    ) -> VoiceChatSession:
        """
        Create a voice chat session.

        Args:
            conversation_id: Conversation ID
            org_id: Organization ID
            user_id: User ID
            config: Voice chat configuration

        Returns:
            Voice chat session
        """
        return await self.voice_engine.create_session(
            conversation_id=conversation_id,
            org_id=org_id,
            user_id=user_id,
            config=config,
        )

    async def process_message(
        self,
        conversation_id: str,
        user_id: str,
        audio_data: bytes,
        audio_format: Literal["mp3", "wav", "ogg", "flac", "webm", "m4a"] = "webm",
        language: str = "en",
        analyst_role: str | None = None,
    ) -> VoiceChatResult:
        """
        Process a voice message end-to-end.

        Flow:
        1. STT: Transcribe audio to text
        2. Chat: Get AI response from text
        3. TTS: Synthesize response to audio

        Args:
            conversation_id: Conversation ID
            user_id: User ID
            audio_data: Raw audio bytes
            audio_format: Audio format
            language: Language code
            analyst_role: Optional analyst role for chat

        Returns:
            Voice chat result with transcript, response, audio, and costs
        """
        # Initialize result
        result: VoiceChatResult = {
            "user_transcript": "",
            "stt_confidence": 0.0,
            "stt_cost_usd": 0.0,
            "assistant_text": "",
            "assistant_thinking": None,
            "assistant_audio": None,
            "assistant_audio_format": "mp3",
            "tts_cost_usd": 0.0,
            "voice_message": None,
            "total_cost_usd": 0.0,
            "stt_error": None,
            "chat_error": None,
            "tts_error": None,
        }

        # Step 1: Speech-to-Text
        try:
            stt_result = await self.voice_engine.speech_to_text(
                audio_data=audio_data,
                audio_format=audio_format,
                language=language,
                include_timestamps=False,
            )

            result["user_transcript"] = stt_result["text"]
            result["stt_confidence"] = stt_result["confidence"]
            result["stt_cost_usd"] = stt_result["cost_usd"]

            logger.info(f"STT: Transcribed to '{stt_result['text'][:50]}...'")

        except Exception as e:
            result["stt_error"] = str(e)
            logger.error(f"STT failed: {e}")
            return result

        # Step 1.5: MAESTRO - Predict agents from transcript
        predicted_analyst_role = analyst_role
        if self.maestro:
            try:
                context = {
                    "user_id": user_id,
                    "session_id": conversation_id,
                }
                
                prediction = await self.maestro.predict(
                    input_text=result["user_transcript"],
                    context=context,
                    max_candidates=5,
                )
                
                # Use top predicted agent if confidence is high
                if prediction["agents"]:
                    top_agent = prediction["agents"][0]
                    if top_agent["confidence"] > 0.75:
                        predicted_analyst_role = top_agent["agent_id"]
                        logger.info(
                            f"MAESTRO: Routing to agent '{predicted_analyst_role}' "
                            f"(confidence: {top_agent['confidence']:.2f})"
                        )
            except Exception as e:
                logger.warning(f"MAESTRO prediction failed: {e}, using default routing")

        # Step 2: Chat (get AI response)
        try:
            message, chat_error = await self.chat_engine.send_message(
                conversation_id=conversation_id,
                user_id=user_id,
                content=result["user_transcript"],
                analyst_role=predicted_analyst_role,  # Use MAESTRO-predicted role
            )

            if chat_error:
                result["chat_error"] = chat_error.get("message", "Unknown error")
                logger.error(f"Chat failed: {result['chat_error']}")
                return result

            if not message:
                result["chat_error"] = "No response from chat engine"
                return result

            # Extract thinking blocks from response (STRAYLIGHT_STANDARDS)
            response_content = message.get("content", "")
            metadata = message.get("metadata", {})
            
            # Try to get thinking from metadata first (already extracted by ChatEngine)
            thinking_content = None
            if isinstance(metadata, dict):
                thinking_content = metadata.get("thinking")
            
            # If not in metadata, extract from content
            if not thinking_content:
                _, thinking_content = extract_thinking(response_content)
            
            # Strip thinking blocks from text (for TTS - don't speak thinking blocks)
            result["assistant_text"] = strip_thinking(response_content)
            result["assistant_thinking"] = thinking_content if thinking_content else None
            
            logger.info(f"Chat: Response '{result['assistant_text'][:50]}...'")
            if thinking_content:
                logger.info(f"Chat: Thinking block extracted ({len(thinking_content)} chars)")

        except Exception as e:
            result["chat_error"] = str(e)
            logger.error(f"Chat failed: {e}")
            return result

        # Step 3: Text-to-Speech
        tts_response: TTSResponse | None = None
        try:
            # Get voice config from session or use default
            session = await self.voice_engine.get_session(
                f"voice_session_{conversation_id}_{user_id}"
            )

            voice_id = "alloy"
            voice_quality = "standard"

            if session:
                config = session.get("config", {})
                voice_id = config.get("voice", voice_id)
                voice_quality = config.get("quality", voice_quality)

            # Synthesize speech
            tts_response = await self.voice_engine.text_to_speech(
                text=result["assistant_text"],
                voice=voice_id,
                quality=voice_quality,  # type: ignore
                audio_format="mp3",  # type: ignore
            )

            result["assistant_audio"] = tts_response["audio_data"]
            result["assistant_audio_format"] = tts_response["audio_format"].value
            result["tts_cost_usd"] = tts_response["cost_usd"]

            logger.info(f"TTS: Synthesized {len(result['assistant_text'])} chars")

        except Exception as e:
            result["tts_error"] = str(e)
            logger.error(f"TTS failed: {e}")
            # Don't return early - we have text response

        # Calculate total cost
        result["total_cost_usd"] = result["stt_cost_usd"] + result["tts_cost_usd"]

        # Save to voice session
        try:
            # Generate session ID (same pattern as VoiceEngine)
            from toolbox.core.deterministic_id import make_uuid

            session_id = make_uuid("voice_session", conversation_id, user_id)

            # Add user message
            await self.voice_engine.add_message(
                session_id=session_id,
                role="user",
                text=result["user_transcript"],
                duration_seconds=stt_result.get("duration_seconds", 0.0),
                stt_confidence=stt_result.get("confidence", 0.0),
            )

            # Add assistant message (only if TTS succeeded and tts_response is defined)
            if result["assistant_audio"] is not None and tts_response is not None:
                voice_message = await self.voice_engine.add_message(
                    session_id=session_id,
                    role="assistant",
                    text=result["assistant_text"],
                    duration_seconds=tts_response.get("duration_seconds", 0.0),
                )
                result["voice_message"] = voice_message

        except Exception as e:
            logger.warning(f"Failed to save voice messages: {e}")

        return result

    async def process_text_only(
        self,
        conversation_id: str,
        user_id: str,
        text: str,
        analyst_role: str | None = None,
    ) -> VoiceChatResult:
        """
        Process text input and return audio output (TTS only).

        Useful for scenarios where you want:
        - Text input -> AI response -> Audio output

        Args:
            conversation_id: Conversation ID
            user_id: User ID
            text: User text input
            analyst_role: Optional analyst role

        Returns:
            Voice chat result
        """
        # Initialize result
        result: VoiceChatResult = {
            "user_transcript": text,
            "stt_confidence": 1.0,
            "stt_cost_usd": 0.0,
            "assistant_text": "",
            "assistant_thinking": None,
            "assistant_audio": None,
            "assistant_audio_format": "mp3",
            "tts_cost_usd": 0.0,
            "voice_message": None,
            "total_cost_usd": 0.0,
            "stt_error": None,
            "chat_error": None,
            "tts_error": None,
        }

        # Step 1: Chat (get AI response)
        try:
            message, chat_error = await self.chat_engine.send_message(
                conversation_id=conversation_id,
                user_id=user_id,
                content=text,
                analyst_role=analyst_role,
            )

            if chat_error:
                result["chat_error"] = chat_error.get("message", "Unknown error")
                return result

            if not message:
                result["chat_error"] = "No response from chat engine"
                return result

            # Extract thinking blocks from response (STRAYLIGHT_STANDARDS)
            response_content = message.get("content", "")
            metadata = message.get("metadata", {})
            
            # Try to get thinking from metadata first (already extracted by ChatEngine)
            thinking_content = None
            if isinstance(metadata, dict):
                thinking_content = metadata.get("thinking")
            
            # If not in metadata, extract from content
            if not thinking_content:
                _, thinking_content = extract_thinking(response_content)
            
            # Strip thinking blocks from text (for TTS - don't speak thinking blocks)
            result["assistant_text"] = strip_thinking(response_content)
            result["assistant_thinking"] = thinking_content if thinking_content else None

        except Exception as e:
            result["chat_error"] = str(e)
            return result

        # Step 2: Text-to-Speech
        tts_response: TTSResponse | None = None
        try:
            # Get voice config
            from toolbox.core.deterministic_id import make_uuid

            session_id = make_uuid("voice_session", conversation_id, user_id)
            session = await self.voice_engine.get_session(session_id)

            voice_id = "alloy"
            voice_quality = "standard"

            if session:
                config = session.get("config", {})
                voice_id = config.get("voice", voice_id)
                voice_quality = config.get("quality", voice_quality)

            # Synthesize speech
            tts_response = await self.voice_engine.text_to_speech(
                text=result["assistant_text"],
                voice=voice_id,
                quality=voice_quality,  # type: ignore
                audio_format="mp3",  # type: ignore
            )

            result["assistant_audio"] = tts_response["audio_data"]
            result["assistant_audio_format"] = tts_response["audio_format"].value
            result["tts_cost_usd"] = tts_response["cost_usd"]

        except Exception as e:
            result["tts_error"] = str(e)

        # Calculate total cost
        result["total_cost_usd"] = result["tts_cost_usd"]

        # Save messages
        try:
            from toolbox.core.deterministic_id import make_uuid

            session_id = make_uuid("voice_session", conversation_id, user_id)

            # Add user message (no audio)
            await self.voice_engine.add_message(
                session_id=session_id,
                role="user",
                text=text,
                audio_url=None,
                duration_seconds=None,
                stt_confidence=1.0,
            )

            # Add assistant message (if TTS succeeded and tts_response is defined)
            if result["assistant_audio"] is not None and tts_response is not None:
                voice_message = await self.voice_engine.add_message(
                    session_id=session_id,
                    role="assistant",
                    text=result["assistant_text"],
                    duration_seconds=tts_response.get("duration_seconds", 0.0),
                )
                result["voice_message"] = voice_message

        except Exception as e:
            logger.warning(f"Failed to save voice messages: {e}")

        return result

    async def get_session(self, session_id: str) -> VoiceChatSession | None:
        """
        Get a voice chat session.

        Args:
            session_id: Session ID

        Returns:
            Voice chat session or None
        """
        return await self.voice_engine.get_session(session_id)

    async def end_session(self, session_id: str) -> None:
        """
        End a voice chat session.

        Args:
            session_id: Session ID
        """
        await self.voice_engine.end_session(session_id)


# =============================================================================
# Factory
# =============================================================================


async def create_voice_chat_engine(
    chat_engine: ChatEngine,
    voice_engine: VoiceEngine,
) -> VoiceChatEngine:
    """
    Factory function to create voice chat engine.

    Args:
        chat_engine: Chat engine
        voice_engine: Voice engine

    Returns:
        Configured VoiceChatEngine instance
    """
    return VoiceChatEngine(
        chat_engine=chat_engine,
        voice_engine=voice_engine,
    )


__all__ = [
    "VoiceChatResult",
    "VoiceChatEngine",
    "create_voice_chat_engine",
]
