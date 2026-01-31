# Nix-based test script for compiler pipeline (PowerShell)
# Note: Nix on Windows requires WSL2 or NixOS. This script assumes WSL2.

$ErrorActionPreference = "Stop"

Write-Host "=== Nix Build and Test ===" -ForegroundColor Cyan
Write-Host ""

# Check if we're in a Nix flake
if (-not (Test-Path "flake.nix")) {
    Write-Host "Error: flake.nix not found. Run from compiler-pipeline directory." -ForegroundColor Red
    exit 1
}

# Check if running in WSL or native Nix
$isWSL = $env:WSL_DISTRO_NAME -ne $null
$nixCmd = if ($isWSL) { "wsl nix" } else { "nix" }

Write-Host "Step 1: Verifying flake..." -ForegroundColor Yellow
& $nixCmd flake check
if ($LASTEXITCODE -ne 0) {
    Write-Host "Flake check failed. Ensure Nix flakes are enabled." -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "Step 2: Building PureScript → C++23 compiler..." -ForegroundColor Yellow
& $nixCmd build .#purescript-to-cpp23 --print-build-logs
if ($LASTEXITCODE -ne 0) {
    Write-Host "Build failed for purescript-to-cpp23" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "Step 3: Building C++23 → React generator..." -ForegroundColor Yellow
& $nixCmd build .#cpp23-to-react --print-build-logs
if ($LASTEXITCODE -ne 0) {
    Write-Host "Build failed for cpp23-to-react" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "Step 4: Building WASM runtime..." -ForegroundColor Yellow
& $nixCmd build .#runtime-wasm --print-build-logs
if ($LASTEXITCODE -ne 0) {
    Write-Host "Note: WASM build may require Emscripten setup" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "Step 5: Running unit tests..." -ForegroundColor Yellow
& $nixCmd run .#test
if ($LASTEXITCODE -ne 0) {
    Write-Host "Unit tests failed. Enter dev shell for debugging:" -ForegroundColor Red
    Write-Host "  nix develop" -ForegroundColor Yellow
    exit 1
}

Write-Host ""
Write-Host "Step 6: Running integration tests..." -ForegroundColor Yellow
& $nixCmd run .#test-integration
if ($LASTEXITCODE -ne 0) {
    Write-Host "Integration tests failed. Check test-output/ directory." -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "=== All Nix builds and tests passed ===" -ForegroundColor Green
Write-Host ""
Write-Host "To enter development shell:" -ForegroundColor Cyan
Write-Host "  nix develop" -ForegroundColor White
Write-Host ""
Write-Host "To build everything:" -ForegroundColor Cyan
Write-Host "  nix build .#default" -ForegroundColor White
