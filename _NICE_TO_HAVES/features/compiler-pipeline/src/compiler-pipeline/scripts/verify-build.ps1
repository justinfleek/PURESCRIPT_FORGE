# Build verification script for Windows
$ErrorActionPreference = "Stop"

Write-Host "=== Build Verification ===" -ForegroundColor Cyan
Write-Host ""

# Check 1: Verify source files exist
Write-Host "Checking source files..." -ForegroundColor Yellow
$requiredFiles = @(
    "purescript-to-cpp23\src\Parser.hs",
    "purescript-to-cpp23\src\Cpp23Generator.hs",
    "purescript-to-cpp23\src\TypeChecker.hs",
    "purescript-to-cpp23\src\Main.hs",
    "cpp23-to-react\src\ReactGenerator.cpp",
    "cpp23-to-react\src\RadixBinder.cpp",
    "cpp23-to-react\src\TailwindGenerator.cpp"
)

$allExist = $true
foreach ($file in $requiredFiles) {
    if (Test-Path $file) {
        Write-Host "  ✓ $file" -ForegroundColor Green
    } else {
        Write-Host "  ✗ $file MISSING" -ForegroundColor Red
        $allExist = $false
    }
}

if (-not $allExist) {
    Write-Host "Missing required files!" -ForegroundColor Red
    exit 1
}

# Check 2: Try to build
Write-Host ""
Write-Host "Attempting build..." -ForegroundColor Yellow
Push-Location purescript-to-cpp23

try {
    Write-Host "  Running: cabal build" -ForegroundColor Cyan
    cabal build 2>&1 | Tee-Object -Variable buildOutput
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✓ Build successful!" -ForegroundColor Green
        
        # Check for executable
        $exe = Get-ChildItem -Path "dist-newstyle" -Filter "purescript-to-cpp23.exe" -Recurse -ErrorAction SilentlyContinue | Select-Object -First 1
        if ($exe) {
            Write-Host "  ✓ Executable found: $($exe.FullName)" -ForegroundColor Green
        } else {
            Write-Host "  ⚠ Executable not found (may need 'cabal install')" -ForegroundColor Yellow
        }
    } else {
        Write-Host "  ✗ Build failed!" -ForegroundColor Red
        Write-Host $buildOutput -ForegroundColor Red
        exit 1
    }
} catch {
    Write-Host "  ✗ Build error: $_" -ForegroundColor Red
    exit 1
} finally {
    Pop-Location
}

# Check 3: Verify test files exist
Write-Host ""
Write-Host "Checking test files..." -ForegroundColor Yellow
if (Test-Path "tests\test_purescript.purs") {
    Write-Host "  ✓ Test file exists" -ForegroundColor Green
} else {
    Write-Host "  ⚠ Test file missing" -ForegroundColor Yellow
}

# Summary
Write-Host ""
Write-Host "=== Verification Complete ===" -ForegroundColor Cyan
Write-Host "Build system: Ready" -ForegroundColor Green
Write-Host ""
Write-Host "Next steps:" -ForegroundColor Yellow
Write-Host "  1. Run: .\scripts\test-quick.ps1" -ForegroundColor White
Write-Host "  2. Or manually: cabal install --installdir=..\bin" -ForegroundColor White
Write-Host "  3. Then test: .\bin\purescript-to-cpp23.exe compile tests\test_purescript.purs test-output\cpp23" -ForegroundColor White
