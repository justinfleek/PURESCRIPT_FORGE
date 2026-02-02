#!/usr/bin/env python3
"""Check if Qwen3-TTS model weights are installed."""

import os
import sys
from pathlib import Path

# Add to path
sys.path.insert(0, str(Path(__file__).parent))

print("=" * 70)
print("QWEN3-TTS MODEL WEIGHTS CHECK")
print("=" * 70)

# Check 1: qwen-tts package
print("\n[1] Checking qwen-tts package...")
try:
    from qwen_tts import Qwen3TTSModel
    print("OK: qwen-tts package is installed")
except ImportError:
    # Try adding source folder to path
    qwen_source = Path(__file__).parent.parent.parent / "Qwen3-TTS-main"
    if qwen_source.exists():
        sys.path.insert(0, str(qwen_source))
        try:
            from qwen_tts import Qwen3TTSModel
            print(f"OK: qwen-tts found in source folder: {qwen_source}")
        except ImportError as e:
            print(f"FAIL: qwen-tts source found but import failed: {e}")
            print("   Missing dependencies - install: librosa, soundfile, transformers, etc.")
            sys.exit(1)
    else:
        print("FAIL: qwen-tts package NOT installed and source not found")
        print("   Install with: pip install qwen-tts")
        print(f"   Or add source to: {qwen_source}")
        sys.exit(1)

# Check 2: Database
print("\n[2] Checking database...")
db_path = os.path.join(os.path.expanduser("~"), ".opencode-sidepanel", "bridge.db")
db_exists = os.path.exists(db_path)
print(f"Database: {db_path}")
print(f"Exists: {db_exists}")

if db_exists:
    import sqlite3
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='tts_models'")
        table_exists = cursor.fetchone() is not None
        
        if table_exists:
            cursor.execute("SELECT id, hf_repo, status, local_path FROM tts_models")
            rows = cursor.fetchall()
            print(f"Models in database: {len(rows)}")
            for row in rows:
                print(f"  - {row[0]}: {row[2]} ({row[3]})")
        else:
            print("tts_models table does not exist")
        conn.close()
    except Exception as e:
        print(f"Error reading database: {e}")

# Check 3: Local models directory
print("\n[3] Checking local models directory...")
base_path = Path(__file__).parent
models_dir = base_path / "models" / "tts"
print(f"Expected path: {models_dir.absolute()}")
print(f"Exists: {models_dir.exists()}")

if models_dir.exists():
    model_dirs = [d for d in models_dir.iterdir() if d.is_dir()]
    print(f"Model directories found: {len(model_dirs)}")
    for d in model_dirs:
        size = sum(f.stat().st_size for f in d.rglob("*") if f.is_file())
        size_gb = size / (1024**3)
        print(f"  - {d.name}: {size_gb:.2f} GB")
else:
    print("Models directory does not exist (will be created on first download)")

# Check 4: HuggingFace cache
print("\n[4] Checking HuggingFace cache...")
hf_cache = Path.home() / ".cache" / "huggingface" / "hub"
print(f"HF cache: {hf_cache}")
print(f"Exists: {hf_cache.exists()}")

if hf_cache.exists():
    qwen_models = list(hf_cache.glob("*Qwen*TTS*"))
    print(f"Qwen TTS models in cache: {len(qwen_models)}")
    for model in qwen_models[:5]:
        size = sum(f.stat().st_size for f in model.rglob("*") if f.is_file())
        size_gb = size / (1024**3)
        print(f"  - {model.name}: {size_gb:.2f} GB")
else:
    print("HuggingFace cache does not exist")

# Check 5: Try to load model
print("\n[5] Attempting to load model...")
try:
    import torch
    print(f"PyTorch version: {torch.__version__}")
    print(f"CUDA available: {torch.cuda.is_available()}")
    
    # Check if we can at least import and create provider
    from toolbox.core.db.sqlite_adapter import SQLiteVoiceDatabase
    from toolbox.engines.voice_local_provider import LocalModelTTSProvider
    import asyncio
    
    async def check_provider():
        db = SQLiteVoiceDatabase(":memory:")
        await db.connect()
        from toolbox.engines.voice_local_provider import init_tts_models_table
        await init_tts_models_table(db)
        
        provider = LocalModelTTSProvider(
            db=db,
            model_id="qwen3-tts-customvoice",
            device="cpu",
        )
        
        record = await provider._get_model_record()
        if record:
            print(f"Model record found: {record['status']}")
            if record.get('local_path'):
                path = Path(record['local_path'])
                print(f"Model path: {path}")
                print(f"Path exists: {path.exists()}")
                if path.exists():
                    size = sum(f.stat().st_size for f in path.rglob("*") if f.is_file())
                    size_gb = size / (1024**3)
                    print(f"Model size: {size_gb:.2f} GB")
        else:
            print("No model record in database")
        
        await db.close()
    
    asyncio.run(check_provider())
    
except Exception as e:
    print(f"Error checking provider: {e}")
    import traceback
    traceback.print_exc()

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("\nTo download model weights:")
print("1. Start the voice engine server")
print("2. Make a TTS request (model will download automatically)")
print("3. Or manually: await provider.ensure_model_downloaded()")
print("\nModel will be downloaded to:")
print(f"  {models_dir.absolute()}/qwen3-tts-customvoice/")
print("\nOr HuggingFace cache:")
print(f"  {hf_cache}/")
