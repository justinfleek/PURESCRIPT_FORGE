#!/usr/bin/env python3
"""Install Qwen3-TTS dependencies manually."""

import subprocess
import sys

deps = [
    "transformers",
    "accelerate", 
    "librosa",
    "soundfile",
    "onnxruntime",
    "einops",
]

print("Installing Qwen3-TTS dependencies...")
print("Note: This may fail due to pip no-index configuration.")
print("If it fails, install manually or fix pip config.\n")

for dep in deps:
    print(f"Installing {dep}...")
    try:
        subprocess.run([sys.executable, "-m", "pip", "install", "--index-url", "https://pypi.org/simple", dep], check=True)
        print(f"  OK: {dep} installed")
    except subprocess.CalledProcessError:
        print(f"  FAIL: {dep} installation failed (may already be installed or network issue)")

print("\nDone! Try importing qwen-tts now.")
