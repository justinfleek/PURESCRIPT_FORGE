#!/bin/bash
# Setup and test script for voice engine

set -e

echo "=========================================="
echo "Voice Engine E2E Test Setup"
echo "=========================================="

# Check Python
echo "Checking Python..."
if ! command -v python3 &> /dev/null; then
    echo "❌ Python 3 not found. Please install Python 3.8+"
    exit 1
fi
python3 --version

# Check pip
echo "Checking pip..."
if ! command -v pip3 &> /dev/null; then
    echo "❌ pip3 not found. Please install pip"
    exit 1
fi

# Install dependencies
echo "Installing Python dependencies..."
cd "$(dirname "$0")"
pip3 install -r requirements.txt

# Check environment
echo "Checking environment..."
if [ -z "$VENICE_API_KEY" ]; then
    echo "⚠️  WARNING: VENICE_API_KEY not set"
    echo "   Set it with: export VENICE_API_KEY=your_key"
    echo "   Some tests will be skipped without it"
else
    echo "✅ VENICE_API_KEY is set"
fi

# Check database path
DB_PATH="${HOME}/.opencode-sidepanel/bridge.db"
echo "Database path: $DB_PATH"
if [ ! -f "$DB_PATH" ]; then
    echo "⚠️  Database file doesn't exist yet. It will be created on first use."
    mkdir -p "$(dirname "$DB_PATH")"
fi

# Run tests
echo ""
echo "=========================================="
echo "Running E2E Tests"
echo "=========================================="
python3 test_e2e.py
