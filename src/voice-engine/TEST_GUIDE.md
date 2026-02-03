# End-to-End Testing Guide

Complete guide for testing the voice engine integration.

## Prerequisites

1. **Python 3.8+** installed
2. **Node.js 18+** installed (for Bridge Server)
3. **VENICE_API_KEY** environment variable set
4. All dependencies installed

## Quick Start

### 1. Install Dependencies

```bash
# Python dependencies
cd src/voice-engine
pip install -r requirements.txt

# Node.js dependencies (if testing Bridge Server integration)
cd ../bridge-server
npm install
```

### 2. Set Environment Variables

```bash
# Windows PowerShell
$env:VENICE_API_KEY = "your_venice_api_key"
$env:VOICE_DB_PATH = "$env:USERPROFILE\.forge-sidepanel\bridge.db"

# Linux/Mac
export VENICE_API_KEY="your_venice_api_key"
export VOICE_DB_PATH="$HOME/.forge-sidepanel/bridge.db"
```

### 3. Start Voice Engine Server

**Option A: Direct Python Server**

```bash
cd src/voice-engine
python -m uvicorn apps.api.src.main:app --host 0.0.0.0 --port 8001
```

**Option B: Using start_server.py**

```bash
cd src/voice-engine
python start_server.py
```

**Option C: Via Bridge Server (automatic)**

```bash
cd src/bridge-server
npm start
# Voice engine will auto-start on port 8001
```

### 4. Run Tests

**In a new terminal:**

```bash
cd src/voice-engine
python test_e2e.py
```

## Test Coverage

The E2E test suite covers:

1. **Health Check** (`/health`)
   - Verifies server is running
   - Checks service status

2. **List Voices** (`/api/voice/voices`)
   - Retrieves available TTS voices
   - Verifies Qwen3 voices are loaded

3. **List Models** (`/api/voice/models`)
   - Lists TTS models in database
   - Shows download status

4. **Text Chat** (`/api/voice/chat/text`)
   - Sends text input
   - Gets AI response via Venice API
   - Receives audio output
   - **Requires VENICE_API_KEY**

5. **Voice Session** (`/api/voice/sessions/:id`)
   - Retrieves session state
   - Tests session management

## Expected Output

### Successful Test Run

```
======================================================================
VOICE ENGINE END-TO-END TEST
======================================================================

OK: VENICE_API_KEY is set (length: 45)

======================================================================
Testing: Python Voice Service (http://localhost:8001)
======================================================================

[TEST] Health check: http://localhost:8001/health
OK: Health check passed: {'status': 'ok', 'service': 'voice-engine'}

[TEST] List voices: http://localhost:8001/api/voice/voices
OK: Found 9 voices: Ryan, Vivian, Sophia, Alex, Emma, James, Maria, David, Luna

[TEST] List models: http://localhost:8001/api/voice/models
OK: Found 1 models
   - Qwen3-TTS 1.7B CustomVoice (ready)

[TEST] Text chat: http://localhost:8001/api/voice/chat/text
OK: Text chat successful
   Assistant text: Hello! I can hear you. How can I help you today?...
   Audio format: mp3
   Audio present: True
   Audio size: 12345 bytes (base64)

[TEST] Voice session: http://localhost:8001/api/voice/sessions/test_session
SKIP: Session not found (expected for new session)

======================================================================
TEST SUMMARY
======================================================================

Python Voice Service:
  OK: health
  OK: list_voices
  OK: list_models
  OK: text_chat
  OK: voice_session

SUCCESS: ALL TESTS PASSED
```

## Troubleshooting

### Server Won't Start

**Error: `VENICE_API_KEY environment variable is required`**
- Set the environment variable before starting
- Check: `echo $VENICE_API_KEY` (Linux/Mac) or `echo $env:VENICE_API_KEY` (PowerShell)

**Error: `ModuleNotFoundError: No module named 'apps'`**
- Make sure you're running from the correct directory
- Try: `cd src/voice-engine && python -m uvicorn apps.api.src.main:app --port 8001`

**Error: Database connection failed**
- Check database path exists: `~/.forge-sidepanel/bridge.db`
- Ensure parent directory exists
- Check file permissions

### Tests Fail

**Health check fails: `All connection attempts failed`**
- Server is not running
- Start the server first (see Step 3)
- Check port 8001 is not in use: `netstat -an | grep 8001`

**Text chat fails: `Venice API error`**
- Check VENICE_API_KEY is correct
- Verify API key has balance
- Check network connectivity

**List models returns empty**
- Models table may be empty (normal for first run)
- Models will be downloaded on first TTS request
- Check database: `sqlite3 ~/.forge-sidepanel/bridge.db "SELECT * FROM tts_models;"`

### Database Issues

**Tables don't exist**
- Tables are created automatically on first use
- Check logs for initialization messages
- Manually initialize: See `INTEGRATION.md`

**Database locked**
- Another process is using the database
- Close Bridge Server if running
- Check for other Python processes

## Manual Testing

### Test Health Endpoint

```bash
curl http://localhost:8001/health
```

Expected:
```json
{"status":"ok","service":"voice-engine"}
```

### Test List Voices

```bash
curl http://localhost:8001/api/voice/voices
```

Expected:
```json
{"voices":["Ryan","Vivian","Sophia","Alex","Emma","James","Maria","David","Luna"]}
```

### Test Text Chat

```bash
curl -X POST http://localhost:8001/api/voice/chat/text \
  -H "Content-Type: application/json" \
  -d '{"text":"Hello, test","conversation_id":"test","voice":"Ryan"}'
```

Expected:
```json
{
  "assistant_text": "Hello! How can I help?",
  "assistant_thinking": null,
  "assistant_audio_base64": "base64_encoded_audio...",
  "assistant_audio_format": "mp3",
  "tts_cost_usd": 0.0,
  "total_cost_usd": 0.0
}
```

## Integration Testing

### Test Bridge Server Integration

1. Start Bridge Server:
```bash
cd src/bridge-server
npm start
```

2. Bridge Server will automatically start voice engine on port 8001

3. Test via Bridge Server proxy:
```bash
curl http://localhost:8765/api/voice/voices
```

4. Run full test suite:
```bash
cd src/voice-engine
BRIDGE_API_URL=http://localhost:8765 python test_e2e.py
```

## Next Steps

After successful E2E tests:

1. ✅ Voice engine is fully integrated
2. ✅ Database is working
3. ✅ Venice API integration is working
4. ✅ TTS/STT providers are functional
5. ✅ Ready for agent training

See `FULL_INTEGRATION.md` for architecture details.
