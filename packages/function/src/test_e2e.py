#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
End-to-End Voice Engine Test

Tests the complete voice chat flow:
1. Health check
2. List voices
3. List models
4. Text-to-speech chat
5. Voice session management
"""

import asyncio
import json
import os
import sys
from pathlib import Path

# Fix Windows console encoding
if sys.platform == 'win32':
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')

import httpx


# Test configuration
BASE_URL = os.getenv("VOICE_API_URL", "http://localhost:8001")
BRIDGE_URL = os.getenv("BRIDGE_API_URL", "http://localhost:8765")


async def test_health(client: httpx.AsyncClient, url: str) -> bool:
    """Test health endpoint."""
    print(f"\n[TEST] Health check: {url}/health")
    try:
        response = await client.get(f"{url}/health")
        if response.status_code == 200:
            print(f"OK: Health check passed: {response.json()}")
            return True
        else:
            print(f"FAIL: Health check failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"FAIL: Health check error: {e}")
        return False


async def test_list_voices(client: httpx.AsyncClient, url: str) -> bool:
    """Test list voices endpoint."""
    print(f"\n[TEST] List voices: {url}/api/voice/voices")
    try:
        response = await client.get(f"{url}/api/voice/voices")
        if response.status_code == 200:
            data = response.json()
            voices = data.get("voices", [])
            print(f"✅ Found {len(voices)} voices: {', '.join(voices)}")
            return len(voices) > 0
        else:
            print(f"❌ List voices failed: {response.status_code} - {response.text}")
            return False
    except Exception as e:
        print(f"❌ List voices error: {e}")
        return False


async def test_list_models(client: httpx.AsyncClient, url: str) -> bool:
    """Test list models endpoint."""
    print(f"\n[TEST] List models: {url}/api/voice/models")
    try:
        response = await client.get(f"{url}/api/voice/models")
        if response.status_code == 200:
            data = response.json()
            models = data.get("models", [])
            print(f"OK: Found {len(models)} models")
            for model in models:
                print(f"   - {model.get('name', 'Unknown')} ({model.get('status', 'unknown')})")
            return True
        else:
            print(f"FAIL: List models failed: {response.status_code} - {response.text}")
            return False
    except Exception as e:
        print(f"FAIL: List models error: {e}")
        return False


async def test_text_chat(client: httpx.AsyncClient, url: str) -> bool:
    """Test text-to-speech chat endpoint."""
    print(f"\n[TEST] Text chat: {url}/api/voice/chat/text")
    try:
        payload = {
            "text": "Hello, this is a test message. Can you hear me?",
            "conversation_id": "test_conversation",
            "voice": "Ryan",
        }
        response = await client.post(
            f"{url}/api/voice/chat/text",
            json=payload,
            timeout=60.0,
        )
        
        if response.status_code == 200:
            data = response.json()
            print(f"OK: Text chat successful")
            print(f"   Assistant text: {data.get('assistant_text', 'N/A')[:100]}...")
            print(f"   Audio format: {data.get('assistant_audio_format', 'N/A')}")
            audio_present = bool(data.get("assistant_audio_base64"))
            print(f"   Audio present: {audio_present}")
            if audio_present:
                audio_len = len(data.get("assistant_audio_base64", ""))
                print(f"   Audio size: {audio_len} bytes (base64)")
            return True
        else:
            print(f"FAIL: Text chat failed: {response.status_code}")
            print(f"   Response: {response.text[:500]}")
            return False
    except httpx.TimeoutException:
        print(f"FAIL: Text chat timed out (60s)")
        return False
    except Exception as e:
        print(f"FAIL: Text chat error: {e}")
        import traceback
        traceback.print_exc()
        return False


async def test_voice_session(client: httpx.AsyncClient, url: str) -> bool:
    """Test voice session management."""
    print(f"\n[TEST] Voice session: {url}/api/voice/sessions/test_session")
    try:
        # Get session
        response = await client.get(f"{url}/api/voice/sessions/test_session")
        if response.status_code == 200:
            data = response.json()
            print(f"OK: Session retrieved")
            print(f"   State: {data.get('state', 'N/A')}")
            print(f"   Conversation ID: {data.get('conversation_id', 'N/A')}")
            return True
        elif response.status_code == 404:
            print(f"SKIP: Session not found (expected for new session)")
            return True  # Not an error, just doesn't exist yet
        else:
            print(f"FAIL: Get session failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"FAIL: Session test error: {e}")
        return False


async def run_tests():
    """Run all end-to-end tests."""
    print("=" * 70)
    print("VOICE ENGINE END-TO-END TEST")
    print("=" * 70)
    
    # Check environment
    venice_key = os.getenv("VENICE_API_KEY")
    if not venice_key:
        print("\n⚠️  WARNING: VENICE_API_KEY not set. Some tests may fail.")
        print("   Set VENICE_API_KEY environment variable to test chat functionality.")
    else:
        print(f"\n✅ VENICE_API_KEY is set (length: {len(venice_key)})")
    
    # Test both direct Python service and Bridge Server proxy
    test_urls = []
    
    # Test Python service directly
    python_url = BASE_URL
    test_urls.append(("Python Voice Service", python_url))
    
    # Test Bridge Server proxy
    bridge_url = BRIDGE_URL
    test_urls.append(("Bridge Server Proxy", bridge_url))
    
    results = {}
    
    async with httpx.AsyncClient() as client:
        for name, url in test_urls:
            print(f"\n{'=' * 70}")
            print(f"Testing: {name} ({url})")
            print('=' * 70)
            
            test_results = {}
            
            # Health check
            test_results["health"] = await test_health(client, url)
            
            if not test_results["health"]:
                print(f"\n⚠️  {name} is not responding. Skipping remaining tests.")
                results[name] = test_results
                continue
            
            # List voices
            test_results["list_voices"] = await test_list_voices(client, url)
            
            # List models
            test_results["list_models"] = await test_list_models(client, url)
            
            # Text chat (requires Venice API key)
            if venice_key:
                test_results["text_chat"] = await test_text_chat(client, url)
            else:
                print(f"\nSKIP: Skipping text chat test (no VENICE_API_KEY)")
                test_results["text_chat"] = None
            
            # Voice session
            test_results["voice_session"] = await test_voice_session(client, url)
            
            results[name] = test_results
    
    # Print summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    
    for name, test_results in results.items():
        print(f"\n{name}:")
        for test_name, result in test_results.items():
            if result is True:
                print(f"  OK: {test_name}")
            elif result is False:
                print(f"  FAIL: {test_name}")
            elif result is None:
                print(f"  SKIP: {test_name} (skipped)")
    
    # Overall status
    all_passed = all(
        all(r for r in test_results.values() if r is not None)
        for test_results in results.values()
    )
    
    if all_passed:
        print("\nSUCCESS: ALL TESTS PASSED")
        return 0
    else:
        print("\nFAILURE: SOME TESTS FAILED")
        return 1


if __name__ == "__main__":
    exit_code = asyncio.run(run_tests())
    sys.exit(exit_code)
