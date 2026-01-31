# Verification Script - Phase 1: Compilation Verification
# Verifies all code compiles correctly (PowerShell version)

$ErrorActionPreference = "Stop"

Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  Phase 1: Compilation Verification" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

# Track results
$script:PurescriptPassed = 0
$script:PurescriptFailed = 0
$script:HaskellPassed = 0
$script:HaskellFailed = 0
$script:Lean4Passed = 0
$script:Lean4Failed = 0

# Function to print status
function Print-Status {
    param(
        [bool]$Success,
        [string]$Message
    )
    if ($Success) {
        Write-Host "✓ $Message" -ForegroundColor Green
    } else {
        Write-Host "✗ $Message" -ForegroundColor Red
    }
}

# Function to check if command exists
function Test-Command {
    param([string]$Command)
    $null = Get-Command $Command -ErrorAction SilentlyContinue
    if (-not $?) {
        Write-Host "Error: $Command not found" -ForegroundColor Red
        Write-Host "Please install $Command to continue verification"
        exit 1
    }
}

Write-Host "Checking required tools..."
Write-Host "Note: Tools can be provided via Nix dev shell: nix develop" -ForegroundColor Yellow
Write-Host ""

# Try to use Nix dev shell if available
$useNix = $false
try {
    $null = Get-Command "nix" -ErrorAction SilentlyContinue
    if ($?) {
        Write-Host "Nix found - will use nix develop for builds" -ForegroundColor Green
        $useNix = $true
    }
} catch {}

if (-not $useNix) {
    # Check for direct tools
    Test-Command "spago"
    Test-Command "cabal"
    # Lean4 check is optional
}
Write-Host ""

# ============================================================================
# PureScript Verification
# ============================================================================
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan
Write-Host "  PureScript Verification" -ForegroundColor Cyan
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan
Write-Host ""

# Bridge Server PureScript
Write-Host "Verifying bridge-server-ps..."
Push-Location "src\bridge-server-ps"
try {
    if ($useNix) {
        $output = nix develop -c spago build 2>&1 | Out-String
    } else {
        $output = spago build 2>&1 | Out-String
    }
    if ($LASTEXITCODE -eq 0) {
        Print-Status $true "bridge-server-ps compiled successfully"
        $script:PurescriptPassed++
    } else {
        Print-Status $false "bridge-server-ps compilation failed"
        $script:PurescriptFailed++
        Write-Host "Build errors:"
        $output | Select-String -Pattern "error" -CaseSensitive:$false
    }
} catch {
    Print-Status $false "bridge-server-ps compilation failed: $_"
    $script:PurescriptFailed++
}
Pop-Location

# OpenCode Plugin PureScript
if (Test-Path "src\opencode-plugin-ps") {
    Write-Host ""
    Write-Host "Verifying opencode-plugin-ps..."
    Push-Location "src\opencode-plugin-ps"
    try {
        $output = spago build 2>&1 | Out-String
        if ($LASTEXITCODE -eq 0) {
            Print-Status $true "opencode-plugin-ps compiled successfully"
            $script:PurescriptPassed++
        } else {
            Print-Status $false "opencode-plugin-ps compilation failed"
            $script:PurescriptFailed++
            Write-Host "Build errors:"
            $output | Select-String -Pattern "error" -CaseSensitive:$false
        }
    } catch {
        Print-Status $false "opencode-plugin-ps compilation failed: $_"
        $script:PurescriptFailed++
    }
    Pop-Location
}

# ============================================================================
# Haskell Verification
# ============================================================================
Write-Host ""
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan
Write-Host "  Haskell Verification" -ForegroundColor Cyan
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan
Write-Host ""

# Bridge Database Haskell
Write-Host "Verifying bridge-database-hs..."
Push-Location "src\bridge-database-hs"
try {
    $output = cabal build 2>&1 | Out-String
    if ($LASTEXITCODE -eq 0) {
        Print-Status $true "bridge-database-hs compiled successfully"
        $script:HaskellPassed++
    } else {
        Print-Status $false "bridge-database-hs compilation failed"
        $script:HaskellFailed++
        Write-Host "Build errors:"
        $output | Select-String -Pattern "error" -CaseSensitive:$false
    }
} catch {
    Print-Status $false "bridge-database-hs compilation failed: $_"
    $script:HaskellFailed++
}
Pop-Location

# Bridge Analytics Haskell
if (Test-Path "src\bridge-analytics-hs") {
    Write-Host ""
    Write-Host "Verifying bridge-analytics-hs..."
    Push-Location "src\bridge-analytics-hs"
    try {
        $output = cabal build 2>&1 | Out-String
        if ($LASTEXITCODE -eq 0) {
            Print-Status $true "bridge-analytics-hs compiled successfully"
            $script:HaskellPassed++
        } else {
            Print-Status $false "bridge-analytics-hs compilation failed"
            $script:HaskellFailed++
            Write-Host "Build errors:"
            $output | Select-String -Pattern "error" -CaseSensitive:$false
        }
    } catch {
        Print-Status $false "bridge-analytics-hs compilation failed: $_"
        $script:HaskellFailed++
    }
    Pop-Location
}

# ============================================================================
# Lean4 Verification
# ============================================================================
Write-Host ""
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan
Write-Host "  Lean4 Verification" -ForegroundColor Cyan
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan
Write-Host ""

# Rules Lean4
Write-Host "Verifying rules-lean..."
Push-Location "src\rules-lean"
try {
    $leanVersion = lean --version 2>&1
    if ($LASTEXITCODE -eq 0) {
        if (Test-Path "lakefile.lean") {
            $output = lake build 2>&1 | Out-String
            if ($LASTEXITCODE -eq 0) {
                Print-Status $true "rules-lean compiled successfully"
                $script:Lean4Passed++
            } else {
                Print-Status $false "rules-lean compilation failed"
                $script:Lean4Failed++
                Write-Host "Build errors:"
                $output | Select-String -Pattern "error" -CaseSensitive:$false
            }
        } else {
            Write-Host "⚠ No lakefile.lean found, skipping Lean4 build" -ForegroundColor Yellow
        }
    } else {
        Write-Host "⚠ Lean4 not found, skipping verification" -ForegroundColor Yellow
    }
} catch {
    Write-Host "⚠ Lean4 not available, skipping verification" -ForegroundColor Yellow
}
Pop-Location

# ============================================================================
# Summary
# ============================================================================
Write-Host ""
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  Verification Summary" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

$totalPassed = $script:PurescriptPassed + $script:HaskellPassed + $script:Lean4Passed
$totalFailed = $script:PurescriptFailed + $script:HaskellFailed + $script:Lean4Failed

Write-Host "PureScript:"
Write-Host "  Passed: $($script:PurescriptPassed)"
Write-Host "  Failed: $($script:PurescriptFailed)"
Write-Host ""
Write-Host "Haskell:"
Write-Host "  Passed: $($script:HaskellPassed)"
Write-Host "  Failed: $($script:HaskellFailed)"
Write-Host ""
Write-Host "Lean4:"
Write-Host "  Passed: $($script:Lean4Passed)"
Write-Host "  Failed: $($script:Lean4Failed)"
Write-Host ""
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan
Write-Host "Total: $totalPassed passed, $totalFailed failed" -ForegroundColor Cyan
Write-Host "────────────────────────────────────────────────────────────────" -ForegroundColor Cyan

if ($totalFailed -eq 0) {
    Write-Host "✓ All verifications passed!" -ForegroundColor Green
    exit 0
} else {
    Write-Host "✗ Some verifications failed" -ForegroundColor Red
    Write-Host ""
    Write-Host "Next steps:"
    Write-Host "1. Review build errors above"
    Write-Host "2. Fix compilation errors"
    Write-Host "3. Re-run verification: .\scripts\verify-compilation.ps1"
    exit 1
}
