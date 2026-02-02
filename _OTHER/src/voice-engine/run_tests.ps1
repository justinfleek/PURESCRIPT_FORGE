# PowerShell script to run E2E tests

Write-Host "=========================================="
Write-Host "Voice Engine E2E Test Runner"
Write-Host "=========================================="

# Check if server is running
Write-Host "Checking if voice engine server is running..."
try {
    $response = Invoke-WebRequest -Uri "http://localhost:8001/health" -TimeoutSec 2 -ErrorAction Stop
    Write-Host "OK: Server is running on port 8001"
} catch {
    Write-Host "WARNING: Server is not running on port 8001"
    Write-Host ""
    Write-Host "To start the server, run:"
    Write-Host "  cd src/voice-engine"
    Write-Host "  python -m uvicorn apps.api.src.main:app --port 8001"
    Write-Host ""
    $start = Read-Host "Start server now? (y/n)"
    if ($start -eq "y") {
        Write-Host "Starting server in background..."
        Start-Process python -ArgumentList "-m", "uvicorn", "apps.api.src.main:app", "--port", "8001" -WindowStyle Hidden
        Write-Host "Waiting for server to start..."
        Start-Sleep -Seconds 5
    } else {
        Write-Host "Skipping tests. Start server manually and run tests again."
        exit 1
    }
}

# Check environment
if (-not $env:VENICE_API_KEY) {
    Write-Host "WARNING: VENICE_API_KEY not set"
    Write-Host "Some tests will be skipped"
    Write-Host ""
}

# Run tests
Write-Host ""
Write-Host "Running E2E tests..."
Write-Host ""

python test_e2e.py

if ($LASTEXITCODE -eq 0) {
    Write-Host ""
    Write-Host "SUCCESS: All tests passed!"
} else {
    Write-Host ""
    Write-Host "FAILURE: Some tests failed. Check output above."
    exit 1
}
