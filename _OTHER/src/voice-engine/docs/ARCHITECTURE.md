# Voice Engine Architecture

Complete architecture documentation for the voice engine.

## Table of Contents

1. [Overview](#overview)
2. [System Architecture](#system-architecture)
3. [Component Details](#component-details)
4. [Data Flow](#data-flow)
5. [Caching Strategy](#caching-strategy)
6. [Performance Characteristics](#performance-characteristics)
7. [Scalability](#scalability)

## Overview

The Voice Engine is a complete voice chat system that:
- Converts speech to text (STT)
- Processes text through AI chat engine
- Converts response to speech (TTS)
- Manages conversations and sessions
- Caches models, audio, and responses

**Technology Stack**:
- **Backend**: Python 3.10+, FastAPI, Uvicorn
- **TTS**: Qwen3-TTS (local), OpenAI, ElevenLabs
- **STT**: OpenAI Whisper, Deepgram, Mock (for testing)
- **Chat**: Venice API (Qwen3-based)
- **Database**: SQLite (via aiosqlite)
- **Caching**: In-memory LRU + TTL caches

## System Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Bridge Server (Express)                   │
│  ┌────────────────────────────────────────────────────────┐  │
│  │         Voice Routes (/api/voice/*)                    │  │
│  │         └─> Proxy to Python Voice Engine              │  │
│  └────────────────────────────────────────────────────────┘  │
└───────────────────────────┬───────────────────────────────────┘
                            │ HTTP Proxy
                            ▼
┌─────────────────────────────────────────────────────────────┐
│              Voice Engine (FastAPI)                         │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  VoiceChatEngine                                      │  │
│  │  ├─> STT Provider (transcribe audio)                 │  │
│  │  ├─> Chat Engine (Venice API)                        │  │
│  │  └─> TTS Provider (synthesize audio)                │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  Caching Layer                                        │  │
│  │  ├─> Model Cache (LRU, max 3 models)                 │  │
│  │  ├─> Audio Cache (TTL 1h, max 1000 entries)         │  │
│  │  └─> Response Cache (TTL 30m, max 5000 entries)      │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  Database (SQLite)                                    │  │
│  │  ├─> voice_chat_sessions                             │  │
│  │  ├─> voice_chat_messages                              │  │
│  │  └─> tts_models                                       │  │
│  └──────────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────────┘
```

## Component Details

### VoiceChatEngine

Orchestrates the complete voice chat flow:
1. Receives audio input
2. Transcribes via STT
3. Sends to chat engine
4. Synthesizes response via TTS
5. Returns audio + transcript

**Key Methods**:
- `process_message()`: Full audio → audio flow
- `process_text_only()`: Text → audio flow

### VoiceEngine

Core voice operations:
- Session management
- TTS/STT coordination
- Quality settings

### TTS Providers

**LocalModelTTSProvider** (Qwen3-TTS):
- Loads models from HuggingFace
- Supports 9 preset voices
- Generates high-quality audio
- Uses model caching

**OpenAITTSProvider**:
- Cloud-based TTS
- Multiple voices
- Fast, but costs per request

**ElevenLabsTTSProvider**:
- Premium voices
- High quality
- Expensive

### STT Providers

**OpenAIWhisperSTTProvider**:
- Cloud-based transcription
- High accuracy
- Costs per minute

**DeepgramSTTProvider**:
- Real-time transcription
- Lower latency
- Competitive pricing

**MockSTTProvider**:
- For testing
- Returns configurable transcript
- No API calls

### Chat Engine

**VeniceChatEngine**:
- Wraps Venice API
- Handles Qwen3 chat templates
- Extracts thinking blocks
- Uses response caching

### Database

**SQLiteVoiceDatabase**:
- Async SQLite operations
- Session persistence
- Message history
- Model metadata

## Data Flow

### Voice Chat Flow

```
User Audio (webm/mp3/wav)
    │
    ▼
[STT Provider]
    │
    ▼
User Transcript (text)
    │
    ▼
[Chat Engine] ──> [Response Cache] ──> Cache Hit? ──> Return Cached
    │                                              │
    └──> Cache Miss ──> [Venice API] ─────────────┘
    │
    ▼
Assistant Text (with thinking blocks filtered)
    │
    ▼
[TTS Provider] ──> [Audio Cache] ──> Cache Hit? ──> Return Cached
    │                                    │
    └──> Cache Miss ──> [Qwen3-TTS] ────┘
    │
    ▼
Assistant Audio (mp3/wav)
    │
    ▼
Response (JSON with transcript + audio)
```

### Caching Flow

**Model Cache**:
```
Request Model
    │
    ▼
[Model Cache] ──> Found? ──> Return Cached Model
    │              │
    └──> Not Found ──> Load from Disk ──> Cache ──> Return
```

**Audio Cache**:
```
Request Audio (text + voice + format)
    │
    ▼
[Audio Cache] ──> Found + Not Expired? ──> Return Cached
    │                    │
    └──> Not Found/Expired ──> Generate ──> Cache ──> Return
```

**Response Cache**:
```
Request Response (conversation + query + analyst)
    │
    ▼
[Response Cache] ──> Found + Not Expired? ──> Return Cached
    │                        │
    └──> Not Found/Expired ──> Call API ──> Cache ──> Return
```

## Caching Strategy

### Model Cache

- **Type**: LRU (Least Recently Used)
- **Size**: Max 3 models
- **Eviction**: When limit reached, evict least recently used
- **Purpose**: Avoid reloading models (expensive operation)

### Audio Cache

- **Type**: TTL + LRU
- **Size**: Max 1000 entries
- **TTL**: 1 hour
- **Key**: SHA256(text + voice + format)
- **Eviction**: TTL expiration + LRU when full
- **Purpose**: Avoid re-synthesizing identical requests

### Response Cache

- **Type**: TTL + LRU
- **Size**: Max 5000 entries
- **TTL**: 30 minutes
- **Key**: SHA256(conversation_id + query + analyst_role)
- **Eviction**: TTL expiration + LRU when full
- **Purpose**: Avoid re-processing identical queries

## Performance Characteristics

### Latency

| Operation | P50 | P95 | P99 | Notes |
|-----------|-----|-----|-----|-------|
| STT (Mock) | 5ms | 10ms | 20ms | Mock provider |
| STT (OpenAI) | 500ms | 2s | 5s | Depends on audio length |
| Chat (Cached) | 1ms | 5ms | 10ms | Cache hit |
| Chat (Venice) | 1s | 5s | 10s | Depends on model |
| TTS (Cached) | 1ms | 5ms | 10ms | Cache hit |
| TTS (Qwen3) | 200ms | 1s | 2s | First request slower |
| TTS (Qwen3, cached model) | 100ms | 500ms | 1s | Model in memory |

### Throughput

- **Sequential**: ~10-20 requests/second (with caching)
- **Concurrent**: Limited by GPU memory (1-3 concurrent TTS requests)

### Memory Usage

- **Model Cache**: ~3-5GB per model (Qwen3-TTS)
- **Audio Cache**: ~1MB per entry (configurable)
- **Response Cache**: ~1KB per entry (configurable)
- **Base Process**: ~500MB

**Total**: ~5-10GB with one model loaded.

## Scalability

### Horizontal Scaling

**Current Limitation**: Model loading is expensive (GPU memory).

**Scaling Strategy**:
1. **Model Server**: Dedicated model server with persistent models
2. **Load Balancer**: Route requests to available model servers
3. **Stateless Workers**: Voice engine workers (no model state)
4. **Shared Cache**: Redis for audio/response caching

### Vertical Scaling

**GPU Memory**: More GPU memory = more concurrent models
**CPU**: More cores = better parallel processing
**RAM**: More RAM = larger caches

### Optimization Opportunities

1. **Model Quantization**: Reduce model size (INT8/INT4)
2. **Batch Processing**: Process multiple requests together
3. **Streaming**: Stream audio as it's generated
4. **Edge Caching**: CDN for common audio responses

## Security

### Current State

- No authentication (all endpoints public)
- No rate limiting
- No input validation (beyond basic checks)

### Planned Improvements

- JWT-based authentication
- Rate limiting per user/IP
- Input sanitization
- Prompt injection protection (already implemented in validation layer)

## Monitoring

### Metrics to Track

- Request latency (p50, p95, p99)
- Cache hit rates
- Error rates
- Memory usage
- GPU utilization
- Model load times

### Logging

- Structured logging (JSON)
- Request IDs for tracing
- Error stack traces
- Performance metrics

## Deployment

### Development

```bash
# Start voice engine
cd src/voice-engine
python -m uvicorn apps.api.src.main:app --port 8001
```

### Production

```bash
# Use gunicorn with uvicorn workers
gunicorn apps.api.src.main:app \
  --workers 4 \
  --worker-class uvicorn.workers.UvicornWorker \
  --bind 0.0.0.0:8001
```

### Docker

```dockerfile
FROM python:3.10-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt
COPY . .
CMD ["uvicorn", "apps.api.src.main:app", "--host", "0.0.0.0", "--port", "8001"]
```

## Future Enhancements

1. **Streaming**: Stream audio as it's generated
2. **Voice Cloning**: Custom voice training
3. **Multi-language**: Better language support
4. **Emotion Detection**: Adjust TTS based on emotion
5. **Real-time**: WebSocket support for real-time chat
