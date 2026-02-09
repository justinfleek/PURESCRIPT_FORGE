#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Qwen3-TTS Integration Test

Tests that Qwen3-TTS is properly integrated and can be used.
"""

import asyncio
import sys
from pathlib import Path

# Fix Windows console encoding
if sys.platform == 'win32':
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')


async def test_qwen_import():
    """Test that qwen-tts can be imported."""
    print("\n[TEST] Importing qwen-tts...")
    try:
        from qwen_tts import Qwen3TTSModel
        print("OK: qwen-tts imported successfully")
        print(f"   Qwen3TTSModel: {Qwen3TTSModel}")
        return True
    except ImportError as e:
        print(f"FAIL: Cannot import qwen-tts: {e}")
        print("   Install with: pip install qwen-tts")
        return False


async def test_torch_import():
    """Test that torch is available."""
    print("\n[TEST] Importing torch...")
    try:
        import torch
        print(f"OK: torch imported successfully")
        print(f"   Version: {torch.__version__}")
        print(f"   CUDA available: {torch.cuda.is_available()}")
        if torch.cuda.is_available():
            print(f"   CUDA device: {torch.cuda.get_device_name(0)}")
        return True
    except ImportError as e:
        print(f"FAIL: Cannot import torch: {e}")
        print("   Install with: pip install torch")
        return False


async def test_provider_creation():
    """Test that LocalModelTTSProvider can be created."""
    print("\n[TEST] Creating LocalModelTTSProvider...")
    try:
        from toolbox.core.db.sqlite_adapter import SQLiteVoiceDatabase
        from toolbox.engines.voice_local_provider import LocalModelTTSProvider
        
        # Create in-memory database for testing
        db = SQLiteVoiceDatabase(":memory:")
        await db.connect()
        
        # Initialize tables
        from toolbox.engines.voice_local_provider import init_tts_models_table
        await init_tts_models_table(db)
        
        # Create provider
        provider = LocalModelTTSProvider(
            db=db,
            model_id="qwen3-tts-customvoice",
            device="cpu",  # Use CPU for testing
        )
        
        print("OK: LocalModelTTSProvider created successfully")
        print(f"   Model ID: {provider.model_id}")
        print(f"   HF Repo: {provider._model_info['hf_repo']}")
        print(f"   Device: {provider.device}")
        
        # Check voices
        voices = provider.get_available_voices()
        print(f"   Available voices: {len(voices)} ({', '.join(voices[:3])}...)")
        
        await db.close()
        return True
    except Exception as e:
        print(f"FAIL: Cannot create provider: {e}")
        import traceback
        traceback.print_exc()
        return False


async def test_model_registry():
    """Test that model registry is correct."""
    print("\n[TEST] Checking model registry...")
    try:
        from toolbox.engines.voice_local_provider import MODELS_REGISTRY
        
        print(f"OK: Found {len(MODELS_REGISTRY)} models in registry")
        for model_id, info in MODELS_REGISTRY.items():
            print(f"   - {model_id}: {info['model_name']}")
            print(f"     Repo: {info['hf_repo']}")
            print(f"     Size: {info['estimated_size_mb']} MB")
        
        # Check default model
        if "qwen3-tts-customvoice" in MODELS_REGISTRY:
            print("OK: Default model (qwen3-tts-customvoice) found in registry")
            return True
        else:
            print("FAIL: Default model not found in registry")
            return False
    except Exception as e:
        print(f"FAIL: Cannot access registry: {e}")
        import traceback
        traceback.print_exc()
        return False


async def run_tests():
    """Run all Qwen3-TTS integration tests."""
    print("=" * 70)
    print("QWEN3-TTS INTEGRATION TEST")
    print("=" * 70)
    
    results = {}
    
    # Test imports
    results["qwen_import"] = await test_qwen_import()
    results["torch_import"] = await test_torch_import()
    
    # Test provider (requires imports)
    if results["qwen_import"]:
        results["provider_creation"] = await test_provider_creation()
        results["model_registry"] = await test_model_registry()
    else:
        print("\nSKIP: Skipping provider tests (qwen-tts not installed)")
        results["provider_creation"] = None
        results["model_registry"] = None
    
    # Print summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    
    for test_name, result in results.items():
        if result is True:
            print(f"OK: {test_name}")
        elif result is False:
            print(f"FAIL: {test_name}")
        elif result is None:
            print(f"SKIP: {test_name}")
    
    # Overall status
    all_passed = all(r for r in results.values() if r is not None)
    
    if all_passed:
        print("\nSUCCESS: All tests passed!")
        print("\nNext steps:")
        print("1. Install dependencies: pip install -r requirements.txt")
        print("2. Set VENICE_API_KEY environment variable")
        print("3. Start server: python -m uvicorn apps.api.src.main:app --port 8001")
        print("4. Run E2E tests: python test_e2e.py")
        return 0
    else:
        print("\nFAILURE: Some tests failed")
        print("\nTo fix:")
        print("1. Install qwen-tts: pip install qwen-tts")
        print("2. Install torch: pip install torch")
        print("3. Run tests again: python test_qwen_integration.py")
        return 1


if __name__ == "__main__":
    exit_code = asyncio.run(run_tests())
    sys.exit(exit_code)
