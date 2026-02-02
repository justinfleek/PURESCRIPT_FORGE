# Voice Engine Integration

Full integration of Python voice engine with Bridge Server.

## Architecture

```
Bridge Server (TypeScript/Express)
  ↓ HTTP Proxy
Python Voice Engine (FastAPI)
  ↓ SQLite
Bridge Server Database (shared)
  ↓ Venice API
LLM Chat Responses
```

## Components

1. **VoiceService** (`integration.ts`): Manages Python voice engine process
2. **Voice Routes** (`routes.ts`): Express routes that proxy to Python service
3. **Python Voice Engine**: FastAPI service with full Qwen3-TTS integration

## Setup

### 1. Install Python Dependencies

```bash
cd src/voice-engine
pip install -r requirements.txt
```

### 2. Set Environment Variables

```bash
export VENICE_API_KEY=your_venice_key
export TTS_PROVIDER=local
export TTS_MODEL_ID=qwen3-tts-customvoice
export TTS_DEVICE=cuda:0
export STT_PROVIDER=mock  # or 'openai', 'deepgram'
```

### 3. Start Bridge Server

The voice service will automatically start when Bridge Server starts (if VENICE_API_KEY is set).

```bash
cd src/bridge-server
npm start
```

## API Endpoints

All endpoints are available at `/api/voice/*`:

- `POST /api/voice/chat` - Process voice message
- `POST /api/voice/chat/text` - Text input with audio output
- `GET /api/voice/models` - List TTS models
- `POST /api/voice/models/download` - Download Qwen3-TTS model
- `GET /api/voice/voices` - List available voices
- `GET /api/voice/sessions/:id` - Get voice session
- `POST /api/voice/sessions/:id/end` - End voice session

## Database Integration

The voice engine uses the same SQLite database as Bridge Server:
- Path: `~/.opencode-sidepanel/bridge.db`
- Tables: `voice_chat_sessions`, `voice_chat_messages`, `tts_models`
- Initialized automatically on first use

## Venice API Integration

Voice chat uses Venice API for LLM responses:
- Automatically extracts thinking blocks (`<think>...</think>`)
- Strips thinking blocks from TTS output
- Returns thinking blocks separately for UI display

## Qwen3-TTS Integration

- Model: Qwen3-TTS-12Hz-1.7B-CustomVoice
- 9 preset voices: Ryan, Vivian, Sophia, Alex, Emma, James, Maria, David, Luna
- Automatic model download on first use (~3.4GB)
- GPU acceleration (CUDA) or CPU fallback

## Troubleshooting

**Voice service fails to start?**
- Check Python is installed and in PATH
- Verify VENICE_API_KEY is set
- Check voice-engine dependencies are installed

**Database errors?**
- Ensure Bridge Server database exists
- Check file permissions on database path

**Model download fails?**
- Check internet connection
- Verify HuggingFace access
- Check disk space (3.4GB required)
