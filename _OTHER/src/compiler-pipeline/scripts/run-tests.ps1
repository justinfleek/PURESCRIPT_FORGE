# Test runner for Windows PowerShell
$ErrorActionPreference = "Stop"

Write-Host "=== Compiler Pipeline Test Runner ===" -ForegroundColor Cyan
Write-Host ""

# Check if we're in the right directory
if (-not (Test-Path "purescript-to-cpp23")) {
    Write-Host "Error: Must run from compiler-pipeline directory" -ForegroundColor Red
    exit 1
}

# Step 1: Build
Write-Host "Step 1: Building..." -ForegroundColor Yellow
Push-Location purescript-to-cpp23

try {
    cabal build 2>&1 | Select-Object -Last 10
    if ($LASTEXITCODE -ne 0) {
        Write-Host "Build failed!" -ForegroundColor Red
        exit 1
    }
    Write-Host "Build successful!" -ForegroundColor Green
} finally {
    Pop-Location
}

# Step 2: Run tests
Write-Host ""
Write-Host "Step 2: Running tests..." -ForegroundColor Yellow
Push-Location purescript-to-cpp23

try {
    cabal test 2>&1 | Select-Object -Last 20
    if ($LASTEXITCODE -ne 0) {
        Write-Host "Tests failed!" -ForegroundColor Red
        exit 1
    }
    Write-Host "All tests passed!" -ForegroundColor Green
} finally {
    Pop-Location
}

# Step 3: Quick integration test
Write-Host ""
Write-Host "Step 3: Quick integration test..." -ForegroundColor Yellow

$testDir = "$env:TEMP\compiler-test-$(Get-Random)"
New-Item -ItemType Directory -Force -Path "$testDir\cpp23" | Out-Null

$testInput = @"
module Test where
x = 42;
f y = y + 1;
"@

$testFile = "$testDir\test.purs"
$testInput | Out-File -FilePath $testFile -Encoding utf8

# Find the built executable
$exe = Get-ChildItem -Path "purescript-to-cpp23" -Filter "purescript-to-cpp23.exe" -Recurse | Select-Object -First 1
if (-not $exe) {
    Write-Host "Executable not found. Run 'cabal install' first." -ForegroundColor Yellow
    exit 0
}

& $exe.FullName compile $testFile "$testDir\cpp23"
if ($LASTEXITCODE -eq 0) {
    $output = Get-ChildItem -Path "$testDir\cpp23" -Recurse
    if ($output.Count -gt 0) {
        Write-Host "Integration test passed!" -ForegroundColor Green
        Write-Host "Generated files:" -ForegroundColor Cyan
        $output | ForEach-Object { Write-Host "  $($_.FullName)" }
    } else {
        Write-Host "Integration test failed: No output files" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "Integration test failed!" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "=== All Tests Complete ===" -ForegroundColor Green
Write-Host "Test output in: $testDir" -ForegroundColor Yellow
