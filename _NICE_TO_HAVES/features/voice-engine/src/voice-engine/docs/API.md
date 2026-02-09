# Voice Engine API Documentation

Complete API reference for the voice engine.

## Table of Contents

1. [Overview](#overview)
2. [Endpoints](#endpoints)
3. [Request/Response Types](#requestresponse-types)
4. [Error Handling](#error-handling)
5. [Authentication](#authentication)
6. [Rate Limiting](#rate-limiting)
7. [Examples](#examples)

## Overview

The Voice Engine API provides endpoints for:
- Voice chat (audio → text → AI → audio)
- Text-to-speech synthesis
- Speech-to-text transcription
- Model management
- Session management

**Base URL**: `http://localhost:8001/api`

## Endpoints

### POST /api/voice/chat

Process voice message end-to-end.

**Request**:
- Method: `POST`
- Content-Type: `multipart/form-data`
- Body:
  - `audio`: Audio file (webm, mp3, wav, ogg, flac, m4a)
  - `conversation_id`: Conversation ID (optional, default: "default")
  - `voice`: Voice name (optional, default: "Ryan")
  - `language`: Language code (optional, default: "en")

**Response**:
```json
{
  "user_transcript": "Hello there",
  "stt_confidence": 0.95,
  "stt_cost_usd": 0.0,
  "assistant_text": "Hi! How can I help?",
  "assistant_thinking": null,
  "assistant_audio": "<base64>",
  "assistant_audio_format": "mp3",
  "tts_cost_usd": 0.0,
  "total_cost_usd": 0.0,
  "stt_error": null,
  "chat_error": null,
  "tts_error": null
}
```

### POST /api/voice/chat/text

Text input with audio output.

**Request**:
```json
{
  "text": "Hello, this is a test",
  "conversation_id": "test",
  "voice": "Ryan"
}
```

**Response**:
```json
{
  "assistant_text": "AI response",
  "assistant_thinking": null,
  "assistant_audio_base64": "<base64>",
  "assistant_audio_format": "mp3",
  "tts_cost_usd": 0.0,
  "total_cost_usd": 0.0
}
```

### GET /api/voice/models

List available TTS models.

**Response**:
```json
{
  "models": [
    {
      "id": "qwen3-tts-customvoice",
      "name": "Qwen3-TTS 1.7B CustomVoice",
      "hf_repo": "Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice",
      "status": "ready",
      "file_size_mb": 3400.0,
      "downloaded_at": "2026-01-30T00:00:00Z"
    }
  ]
}
```

### POST /api/voice/models/download

Download TTS model.

**Request**:
```json
{
  "model_id": "qwen3-tts-customvoice"
}
```

**Response**:
```json
{
  "status": "downloading",
  "model_id": "qwen3-tts-customvoice",
  "message": "Model download started"
}
```

### GET /api/voice/voices

List available voices.

**Response**:
```json
{
  "voices": ["Ryan", "Vivian", "Sophia", "Alex", "Emma", "James", "Maria", "David", "Luna"]
}
```

### GET /api/voice/sessions/:id

Get voice session.

**Response**:
```json
{
  "id": "session_123",
  "conversation_id": "conv_456",
  "state": "idle",
  "total_audio_seconds": 120.5,
  "started_at": "2026-01-30T00:00:00Z"
}
```

### POST /api/voice/sessions/:id/end

End voice session.

**Response**:
```json
{
  "status": "ended",
  "session_id": "session_123"
}
```

## Request/Response Types

### VoiceChatResponse

```typescript
interface VoiceChatResponse {
  user_transcript: string;
  stt_confidence: number;
  stt_cost_usd: number;
  assistant_text: string;
  assistant_thinking: string | null;
  assistant_audio: string | null;  // base64
  assistant_audio_format: string;
  tts_cost_usd: number;
  total_cost_usd: number;
  stt_error: string | null;
  chat_error: string | null;
  tts_error: string | null;
}
```

### TextChatResponse

```typescript
interface TextChatResponse {
  assistant_text: string;
  assistant_thinking: string | null;
  assistant_audio_base64: string;
  assistant_audio_format: string;
  tts_cost_usd: number;
  total_cost_usd: number;
}
```

## Error Handling

All endpoints return standard HTTP status codes:

- `200 OK`: Success
- `400 Bad Request`: Invalid request parameters
- `404 Not Found`: Resource not found
- `500 Internal Server Error`: Server error
- `503 Service Unavailable`: Service not ready

Error responses:
```json
{
  "error": "Error code",
  "message": "Human-readable error message",
  "details": {}
}
```

## Authentication

Currently, authentication is not implemented. All endpoints are publicly accessible.

**TODO**: Add JWT-based authentication.

## Rate Limiting

Rate limiting is not currently implemented.

**TODO**: Add rate limiting per user/IP.

## Examples

### Python

```python
import httpx

async def voice_chat(audio_bytes: bytes):
    async with httpx.AsyncClient() as client:
        files = {"audio": ("audio.webm", audio_bytes, "audio/webm")}
        data = {
            "conversation_id": "test",
            "voice": "Ryan",
            "language": "en",
        }
        response = await client.post(
            "http://localhost:8001/api/voice/chat",
            files=files,
            data=data,
        )
        return response.json()
```

### JavaScript

```javascript
async function voiceChat(audioBlob) {
  const formData = new FormData();
  formData.append('audio', audioBlob, 'recording.webm');
  formData.append('conversation_id', 'test');
  formData.append('voice', 'Ryan');
  
  const response = await fetch('http://localhost:8001/api/voice/chat', {
    method: 'POST',
    body: formData,
  });
  
  return await response.json();
}
```

### cURL

```bash
curl -X POST http://localhost:8001/api/voice/chat/text \
  -H "Content-Type: application/json" \
  -d '{
    "text": "Hello, test",
    "conversation_id": "test",
    "voice": "Ryan"
  }'
```

## Caching

The API uses caching for:
- **Model instances**: Cached in memory (LRU, max 3 models)
- **Audio synthesis**: Cached by (text, voice, format) hash (TTL: 1 hour)
- **Chat responses**: Cached by (conversation, query, analyst) hash (TTL: 30 minutes)

Cache statistics available via internal endpoints (not exposed in public API).

## Performance

Expected latencies:
- **STT**: < 2 seconds (p95)
- **Chat**: Depends on Venice API (typically 1-5 seconds)
- **TTS**: < 1 second (p95) with caching, < 5 seconds without

Throughput:
- **Concurrent requests**: Limited by model loading (GPU memory)
- **Sequential requests**: ~10-20 requests/second (with caching)

## Memory Usage

- **Model cache**: ~3-5GB per model (Qwen3-TTS)
- **Audio cache**: ~1MB per entry (configurable)
- **Response cache**: ~1KB per entry (configurable)

Total memory: ~5-10GB with one model loaded.
