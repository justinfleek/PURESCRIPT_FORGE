# Voice Engine Quick Start

Get voice chat with Qwen3-TTS running in 5 minutes.

## Prerequisites

- Python 3.11+
- CUDA-capable GPU (optional, CPU works but slower)
- 4GB+ free disk space (for Qwen3-TTS model)

## Installation

```bash
cd src/voice-engine
pip install -r requirements.txt
```

## Configuration

Create `.env` file:

```bash
TTS_PROVIDER=local
TTS_MODEL_ID=qwen3-tts-customvoice
TTS_DEVICE=cuda:0
STT_PROVIDER=mock
```

## Start Server

```bash
cd apps/api
python -m src.main
```

Server starts on `http://localhost:8000`

## Test It

### 1. Health Check

```bash
curl http://localhost:8000/health
```

### 2. List Voices

```bash
curl http://localhost:8000/api/voice/voices
```

### 3. Send Voice Message (Text Input)

```bash
curl -X POST http://localhost:8000/api/voice/chat/text \
  -H "Content-Type: application/json" \
  -d '{"text": "Hello, this is a test", "conversation_id": "test"}'
```

### 4. Send Voice Message (Audio)

```bash
curl -X POST http://localhost:8000/api/voice/chat \
  -F "audio=@recording.webm" \
  -F "conversation_id=test" \
  -F "voice=Ryan"
```

## Frontend Integration

See `INTEGRATION.md` for complete frontend integration examples.

## Troubleshooting

**Model download fails?**
- Check internet connection
- Verify HuggingFace access
- Check disk space

**GPU not available?**
- Set `TTS_DEVICE=cpu` in `.env`
- Note: CPU inference is slower

**Import errors?**
- Ensure you're in the `src/voice-engine` directory
- Check Python path includes `src/voice-engine`

## Next Steps

- Read `INTEGRATION.md` for complete integration guide
- Read `README.md` for architecture overview
- See `SETUP_COMPLETE.md` for what was integrated
