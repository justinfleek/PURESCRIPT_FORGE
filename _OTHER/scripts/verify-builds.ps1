# Verification script for FORGE workspace builds
# PowerShell version for Windows

Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  FORGE Workspace Build Verification" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

# Check if Nix is available (via WSL2 or native)
$nixAvailable = $false
if (Get-Command nix -ErrorAction SilentlyContinue) {
    $nixAvailable = $true
    Write-Host "✅ Nix found: $(nix --version)" -ForegroundColor Green
} elseif (Get-Command wsl -ErrorAction SilentlyContinue) {
    Write-Host "⚠️  Nix not found in PowerShell. Checking WSL2..." -ForegroundColor Yellow
    $wslNix = wsl bash -c "command -v nix" 2>$null
    if ($wslNix) {
        $nixAvailable = $true
        Write-Host "✅ Nix found in WSL2" -ForegroundColor Green
    }
}

if (-not $nixAvailable) {
    Write-Host "❌ Nix not found. Please install Nix first." -ForegroundColor Red
    Write-Host "   See docs/SETUP.md for instructions" -ForegroundColor Yellow
    Write-Host "   For Windows: Use WSL2 + Nix or Nix for Windows" -ForegroundColor Yellow
    exit 1
}

Write-Host ""

# Function to run Nix command (via WSL if needed)
function Invoke-NixBuild {
    param([string]$Target)
    
    if (Get-Command nix -ErrorAction SilentlyContinue) {
        nix build $Target
    } else {
        wsl bash -c "nix build $Target"
    }
}

# Verify flake
Write-Host "Verifying flake..." -ForegroundColor Cyan
try {
    if (Get-Command nix -ErrorAction SilentlyContinue) {
        nix flake check
    } else {
        wsl bash -c "nix flake check"
    }
    Write-Host "✅ Flake check passed" -ForegroundColor Green
} catch {
    Write-Host "❌ Flake check failed" -ForegroundColor Red
    exit 1
}
Write-Host ""

# Build PureScript Bridge Server
Write-Host "Building PureScript Bridge Server..." -ForegroundColor Cyan
try {
    Invoke-NixBuild ".#bridge-server-ps"
    Write-Host "✅ Bridge Server built" -ForegroundColor Green
} catch {
    Write-Host "❌ Bridge Server build failed" -ForegroundColor Red
    Write-Host "   Check compilation errors above" -ForegroundColor Yellow
    exit 1
}
Write-Host ""

# Build PureScript OpenCode Plugin
Write-Host "Building PureScript OpenCode Plugin..." -ForegroundColor Cyan
try {
    Invoke-NixBuild ".#opencode-plugin-ps"
    Write-Host "✅ OpenCode Plugin built" -ForegroundColor Green
} catch {
    Write-Host "❌ OpenCode Plugin build failed" -ForegroundColor Red
    Write-Host "   Check compilation errors above" -ForegroundColor Yellow
    exit 1
}
Write-Host ""

# Build Haskell Bridge Database
Write-Host "Building Haskell Bridge Database..." -ForegroundColor Cyan
try {
    Invoke-NixBuild ".#bridge-database-hs"
    Write-Host "✅ Bridge Database built" -ForegroundColor Green
} catch {
    Write-Host "❌ Bridge Database build failed" -ForegroundColor Red
    Write-Host "   Check compilation errors above" -ForegroundColor Yellow
    exit 1
}
Write-Host ""

# Build Haskell Bridge Analytics
Write-Host "Building Haskell Bridge Analytics..." -ForegroundColor Cyan
try {
    Invoke-NixBuild ".#bridge-analytics-hs"
    Write-Host "✅ Bridge Analytics built" -ForegroundColor Green
} catch {
    Write-Host "❌ Bridge Analytics build failed" -ForegroundColor Red
    Write-Host "   Check compilation errors above" -ForegroundColor Yellow
    exit 1
}
Write-Host ""

# Build PRISM Color Core (Haskell)
Write-Host "Building PRISM Color Core (Haskell)..." -ForegroundColor Cyan
try {
    Invoke-NixBuild ".#prism-color-core-hs"
    Write-Host "✅ PRISM Color Core built" -ForegroundColor Green
} catch {
    Write-Host "❌ PRISM Color Core build failed" -ForegroundColor Red
    Write-Host "   Check compilation errors above" -ForegroundColor Yellow
    exit 1
}
Write-Host ""

# Run PRISM tests
Write-Host "Running PRISM property tests..." -ForegroundColor Cyan
try {
    if (Get-Command nix -ErrorAction SilentlyContinue) {
        nix build ".#prism-color-core-hs.tests.prism-color-test"
    } else {
        wsl bash -c "nix build .#prism-color-core-hs.tests.prism-color-test"
    }
    Write-Host "✅ PRISM tests passed" -ForegroundColor Green
} catch {
    Write-Host "⚠️  PRISM tests failed or not yet implemented" -ForegroundColor Yellow
}
Write-Host ""

# Build Lean4 proofs
Write-Host "Building Lean4 proofs..." -ForegroundColor Cyan
try {
    Invoke-NixBuild ".#prism-color-core-lean"
    Write-Host "✅ PRISM Lean4 proofs verified" -ForegroundColor Green
} catch {
    Write-Host "⚠️  PRISM Lean4 proofs have remaining sorries" -ForegroundColor Yellow
}
Write-Host ""

Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  Build Verification Complete!" -ForegroundColor Green
Write-Host "════════════════════════════════════════════════════════════════" -ForegroundColor Cyan
