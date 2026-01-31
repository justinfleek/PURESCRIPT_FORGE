# PowerShell setup and test script for voice engine

Write-Host "=========================================="
Write-Host "Voice Engine E2E Test Setup"
Write-Host "=========================================="

# Check Python
Write-Host "Checking Python..."
try {
    $pythonVersion = python --version 2>&1
    Write-Host "✅ $pythonVersion"
} catch {
    Write-Host "❌ Python not found. Please install Python 3.8+"
    exit 1
}

# Check pip
Write-Host "Checking pip..."
try {
    pip --version | Out-Null
    Write-Host "✅ pip is available"
} catch {
    Write-Host "❌ pip not found. Please install pip"
    exit 1
}

# Install dependencies
Write-Host "Installing Python dependencies..."
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $scriptDir
pip install -r requirements.txt

# Check environment
Write-Host "Checking environment..."
if (-not $env:VENICE_API_KEY) {
    Write-Host "⚠️  WARNING: VENICE_API_KEY not set"
    Write-Host "   Set it with: `$env:VENICE_API_KEY='your_key'"
    Write-Host "   Some tests will be skipped without it"
} else {
    Write-Host "✅ VENICE_API_KEY is set"
}

# Check database path
$dbPath = Join-Path $env:USERPROFILE ".opencode-sidepanel\bridge.db"
Write-Host "Database path: $dbPath"
if (-not (Test-Path $dbPath)) {
    Write-Host "⚠️  Database file doesn't exist yet. It will be created on first use."
    $dbDir = Split-Path -Parent $dbPath
    if (-not (Test-Path $dbDir)) {
        New-Item -ItemType Directory -Path $dbDir -Force | Out-Null
    }
}

# Run tests
Write-Host ""
Write-Host "=========================================="
Write-Host "Running E2E Tests"
Write-Host "=========================================="
python test_e2e.py
