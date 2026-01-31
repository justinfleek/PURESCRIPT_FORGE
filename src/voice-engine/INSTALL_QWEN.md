# Installing qwen-tts - Network Issue Detected

## Problem

pip cannot access PyPI due to proxy/network configuration issues:
- Proxy connection refused errors
- Cannot find qwen-tts package (may be network-related)

## Solutions

### Option 1: Install Manually (Recommended)

Since there are network/proxy issues, install manually:

```bash
# Try direct install (if network allows)
pip install qwen-tts

# Or with explicit version
pip install qwen-tts==0.0.5

# Or bypass proxy
pip install --trusted-host pypi.org --trusted-host pypi.python.org --trusted-host files.pythonhosted.org qwen-tts
```

### Option 2: Install from GitHub (if network allows)

```bash
pip install git+https://github.com/QwenLM/Qwen3-TTS.git
```

### Option 3: Fix Proxy Configuration

If you have a proxy, configure pip:

```bash
# Set proxy environment variables
$env:HTTP_PROXY = "http://proxy:port"
$env:HTTPS_PROXY = "http://proxy:port"

# Or configure pip
pip config set global.proxy http://proxy:port
```

### Option 4: Use Alternative Package Manager

If pip continues to fail, try:
- conda (if available)
- Direct download from PyPI and install locally

## Verification

After installation, verify:

```bash
python -c "from qwen_tts import Qwen3TTSModel; print('OK: qwen-tts installed')"
```

## Current Status

- ✅ Integration code: Ready
- ✅ Dependencies listed: qwen-tts in requirements.txt
- ❌ Package installation: Blocked by network/proxy
- ⏳ Model weights: Will download automatically after package install

## Next Steps

1. Fix network/proxy configuration OR install manually
2. Run: `pip install qwen-tts`
3. Verify: `python check_model_weights.py`
4. Start server: Model will download on first use
