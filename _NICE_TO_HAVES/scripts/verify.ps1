# PowerShell verification script for FORGE workspace (Windows)

Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  FORGE Workspace Verification" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

# Check if WSL2 is available
$wslAvailable = Get-Command wsl -ErrorAction SilentlyContinue
if (-not $wslAvailable) {
    Write-Host "❌ WSL2 not found. Please install WSL2 first." -ForegroundColor Red
    Write-Host "   See docs/SETUP.md for instructions" -ForegroundColor Yellow
    exit 1
}

Write-Host "✅ WSL2 found" -ForegroundColor Green
Write-Host ""

# Check Nix in WSL2
Write-Host "Checking Nix in WSL2..."
$nixCheck = wsl bash -c "command -v nix" 2>&1
if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ Nix not found in WSL2. Please install Nix." -ForegroundColor Red
    Write-Host "   See docs/SETUP.md for instructions" -ForegroundColor Yellow
    exit 1
}

Write-Host "✅ Nix found in WSL2" -ForegroundColor Green
Write-Host ""

# Run verification in WSL2
Write-Host "Running verification in WSL2..."
wsl bash scripts/verify.sh

if ($LASTEXITCODE -ne 0) {
    Write-Host ""
    Write-Host "❌ Verification failed" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  All verifications passed!" -ForegroundColor Green
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
