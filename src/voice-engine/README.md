# Voice Engine - Qwen3 Integration

Complete voice chat system with Qwen3-TTS integration, prompt injection protection, and voice controls.

## Features

- **Voice-to-Voice AI Chat**: Full STT → Chat → TTS pipeline
- **Qwen3-TTS Integration**: Local, free, open-source TTS with 9 voice presets
- **Prompt Injection Protection**: 100+ injection patterns detected and sanitized
- **Voice Controls**: Browser Web Speech API integration
- **Modular Providers**: Swap TTS/STT providers (OpenAI, ElevenLabs, Deepgram, Local)

## Quick Start

### Installation

```bash
cd src/voice-engine
pip install -r requirements.txt
```

### Environment Variables

```bash
# TTS Provider (local uses Qwen3-TTS)
export TTS_PROVIDER=local
export TTS_DEVICE=cuda:0  # or 'cpu'

# STT Provider
export STT_PROVIDER=mock  # or 'openai', 'deepgram'

# Optional: API keys for cloud providers
export OPENAI_API_KEY=...
export DEEPGRAM_API_KEY=...
```

### Usage

```python
from toolbox.engines.voice import VoiceEngine
from toolbox.engines.voice_chat import VoiceChatEngine
from toolbox.engines.voice_tts_providers import create_tts_provider
from toolbox.engines.voice_stt_providers import create_stt_provider

# Create providers
tts = create_tts_provider("local", model_id="qwen3-tts-customvoice", db=db)
stt = create_stt_provider("mock")

# Create voice engine
voice_engine = VoiceEngine(db=db, tts_provider=tts, stt_provider=stt)

# Create voice chat engine (integrates with chat)
voice_chat = VoiceChatEngine(chat_engine=chat_engine, voice_engine=voice_engine)

# Process voice message
result = await voice_chat.process_message(
    conversation_id="conv_123",
    user_id="user_456",
    audio_data=audio_bytes,
)
```

## Components

### Voice Engine (`toolbox/engines/voice/`)
- `engine.py`: Core VoiceEngine class
- `types.py`: Type definitions
- `protocols.py`: Database and provider protocols
- `schema.py`: Database schema

### Voice Chat Engine (`toolbox/engines/`)
- `voice_chat.py`: Integrates ChatEngine + VoiceEngine

### TTS Providers (`toolbox/engines/`)
- `voice_tts_providers.py`: OpenAI, ElevenLabs, Mock providers
- `voice_local_provider/`: Qwen3-TTS local provider

### STT Providers (`toolbox/engines/`)
- `voice_stt_providers.py`: OpenAI Whisper, Deepgram, Mock providers

### Qwen3 Integration (`toolbox/llm/`)
- `chat_template.py`: Qwen3/ChatML format parser
- `think_filter.py`: Streaming filter for `<think>` blocks

### Prompt Injection Protection (`toolbox/core/validation/`)
- `sanitizers.py`: Text sanitization and normalization
- `constants.py`: Injection patterns (100+ patterns)

### API Routes (`apps/api/src/routes/`)
- `voice.py`: FastAPI routes for voice chat

### UI Components (`ui/`)
- `VoiceController.js`: Web Speech API FFI bindings

## Qwen3 Voices

9 preset speakers available:

- Ryan (Male, Neutral)
- Vivian (Female, Energetic)
- Sophia (Female, Calm)
- Alex (Male, Professional)
- Emma (Female, Friendly)
- James (Male, Authoritative)
- Maria (Female, Warm)
- David (Male, Casual)
- Luna (Female, Soft)

## Integration with Bridge Server

The voice engine can be integrated with the Bridge Server by adding FastAPI routes:

```python
from fastapi import FastAPI
from apps.api.src.routes.voice import router as voice_router

app = FastAPI()
app.include_router(voice_router)
```

## Documentation

See `docs/VOICE_CHAT.md` for complete documentation.
