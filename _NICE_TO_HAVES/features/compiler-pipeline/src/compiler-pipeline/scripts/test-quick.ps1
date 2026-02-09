# Quick test script for Windows PowerShell
$ErrorActionPreference = "Stop"

Write-Host "=== Quick Build Test ===" -ForegroundColor Cyan

# Find binaries
$psToCpp = $null
$cppToReact = $null

if (Test-Path ".\result\bin\purescript-to-cpp23.exe") {
    $psToCpp = ".\result\bin\purescript-to-cpp23.exe"
    $cppToReact = ".\result\bin\cpp23-to-react.exe"
    Write-Host "Using Nix build result"
} elseif (Test-Path ".\bin\purescript-to-cpp23.exe") {
    $psToCpp = ".\bin\purescript-to-cpp23.exe"
    $cppToReact = ".\bin\cpp23-to-react.exe"
    Write-Host "Using local binaries"
} elseif (Get-Command purescript-to-cpp23 -ErrorAction SilentlyContinue) {
    $psToCpp = "purescript-to-cpp23"
    $cppToReact = "cpp23-to-react"
    Write-Host "Using system binaries"
} else {
    Write-Host "Building compiler pipeline..." -ForegroundColor Yellow
    nix build .#compiler-pipeline
    if ($LASTEXITCODE -ne 0) {
        Write-Host "Build failed!" -ForegroundColor Red
        exit 1
    }
    $psToCpp = ".\result\bin\purescript-to-cpp23.exe"
    $cppToReact = ".\result\bin\cpp23-to-react.exe"
}

# Create test output directory
$testDir = "$env:TEMP\compiler-pipeline-test-$(Get-Random)"
New-Item -ItemType Directory -Force -Path "$testDir\cpp23" | Out-Null
New-Item -ItemType Directory -Force -Path "$testDir\react" | Out-Null

Write-Host "Testing PureScript → C++23 compilation..." -ForegroundColor Cyan
& $psToCpp compile "tests\test_purescript.purs" "$testDir\cpp23"
if ($LASTEXITCODE -ne 0) {
    Write-Host "PureScript → C++23 compilation failed!" -ForegroundColor Red
    exit 1
}

# Find generated C++ files
$cppFiles = Get-ChildItem -Path "$testDir\cpp23" -Filter "*.cpp" -Recurse
$hppFiles = Get-ChildItem -Path "$testDir\cpp23" -Filter "*.hpp" -Recurse

if ($cppFiles.Count -eq 0 -and $hppFiles.Count -eq 0) {
    Write-Host "No C++23 output files generated!" -ForegroundColor Red
    Write-Host "Generated files:" -ForegroundColor Yellow
    Get-ChildItem -Path "$testDir\cpp23" -Recurse
    exit 1
}

Write-Host "C++23 files generated:" -ForegroundColor Green
$cppFiles | ForEach-Object { Write-Host "  $($_.FullName)" }
$hppFiles | ForEach-Object { Write-Host "  $($_.FullName)" }

$cppFile = if ($cppFiles.Count -gt 0) { $cppFiles[0].FullName } else { $null }

if ($cppFile) {
    Write-Host "Testing C++23 → React generation..." -ForegroundColor Cyan
    & $cppToReact $cppFile "$testDir\react"
    if ($LASTEXITCODE -ne 0) {
        Write-Host "C++23 → React generation failed!" -ForegroundColor Red
        exit 1
    }
    
    $reactFiles = Get-ChildItem -Path "$testDir\react" -Filter "*.tsx" -Recurse
    if ($reactFiles.Count -eq 0) {
        $reactFiles = Get-ChildItem -Path "$testDir\react" -Filter "*.jsx" -Recurse
    }
    
    if ($reactFiles.Count -eq 0) {
        Write-Host "No React output files generated!" -ForegroundColor Red
        Write-Host "Generated files:" -ForegroundColor Yellow
        Get-ChildItem -Path "$testDir\react" -Recurse
        exit 1
    }
    
    Write-Host "React files generated:" -ForegroundColor Green
    $reactFiles | ForEach-Object { Write-Host "  $($_.FullName)" }
}

Write-Host ""
Write-Host "=== Test Results ===" -ForegroundColor Cyan
Write-Host "C++23 Output: $testDir\cpp23" -ForegroundColor Green
Write-Host "React Output: $testDir\react" -ForegroundColor Green
Write-Host ""
Write-Host "Quick test passed!" -ForegroundColor Green
Write-Host "Test files preserved in: $testDir" -ForegroundColor Yellow
