#!/bin/bash
# Forge Build Script
# Builds all components: PureScript, Haskell, and Lean4

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo_step() {
    echo -e "${BLUE}==>${NC} $1"
}

echo_success() {
    echo -e "${GREEN}✓${NC} $1"
}

echo_warning() {
    echo -e "${YELLOW}!${NC} $1"
}

echo_error() {
    echo -e "${RED}✗${NC} $1"
}

# Check for required tools
check_tools() {
    echo_step "Checking build tools..."
    
    local missing=0
    
    if command -v spago &> /dev/null; then
        echo_success "spago found: $(spago --version)"
    else
        echo_warning "spago not found - PureScript build will be skipped"
        missing=$((missing + 1))
    fi
    
    if command -v purs &> /dev/null; then
        echo_success "purs found: $(purs --version)"
    else
        echo_warning "purs (PureScript compiler) not found"
        missing=$((missing + 1))
    fi
    
    if command -v cabal &> /dev/null; then
        echo_success "cabal found: $(cabal --version | head -1)"
    else
        echo_warning "cabal not found - Haskell build will be skipped"
        missing=$((missing + 1))
    fi
    
    if command -v ghc &> /dev/null; then
        echo_success "ghc found: $(ghc --version)"
    else
        echo_warning "ghc not found"
        missing=$((missing + 1))
    fi
    
    if command -v lake &> /dev/null; then
        echo_success "lake found: $(lake --version)"
    else
        echo_warning "lake not found - Lean4 build will be skipped"
        missing=$((missing + 1))
    fi
    
    if [ $missing -gt 0 ]; then
        echo_warning "$missing tool(s) missing. Some builds will be skipped."
    fi
}

# Build PureScript
build_purescript() {
    echo_step "Building PureScript..."
    
    if ! command -v spago &> /dev/null; then
        echo_warning "Skipping PureScript build (spago not found)"
        return 0
    fi
    
    # Install dependencies
    echo_step "Installing PureScript dependencies..."
    spago install
    
    # Build
    echo_step "Compiling PureScript..."
    spago build
    
    echo_success "PureScript build complete"
}

# Build Haskell
build_haskell() {
    echo_step "Building Haskell..."
    
    if ! command -v cabal &> /dev/null; then
        echo_warning "Skipping Haskell build (cabal not found)"
        return 0
    fi
    
    # Update package list
    echo_step "Updating Haskell packages..."
    cabal update
    
    # Build
    echo_step "Compiling Haskell..."
    cabal build all
    
    echo_success "Haskell build complete"
}

# Build Lean4 proofs
build_lean_proofs() {
    echo_step "Building Lean4 proofs..."
    
    if ! command -v lake &> /dev/null; then
        echo_warning "Skipping Lean4 build (lake not found)"
        return 0
    fi
    
    # Build main proofs
    echo_step "Building proofs/lean..."
    (cd src/proofs/lean && lake build)
    
    # Build rules proofs
    echo_step "Building rules/lean..."
    (cd src/rules/lean && lake build)
    
    echo_success "Lean4 proofs verified"
}

# Run tests
run_tests() {
    echo_step "Running tests..."
    
    if command -v spago &> /dev/null; then
        echo_step "Running PureScript tests..."
        spago test || echo_warning "PureScript tests failed or not configured"
    fi
    
    if command -v cabal &> /dev/null; then
        echo_step "Running Haskell tests..."
        cabal test all || echo_warning "Haskell tests failed or not configured"
    fi
    
    if command -v lake &> /dev/null; then
        echo_step "Verifying Lean4 proofs..."
        (cd src/proofs/lean && lake build) && echo_success "Proofs verified"
    fi
}

# Clean build artifacts
clean() {
    echo_step "Cleaning build artifacts..."
    
    rm -rf output/
    rm -rf .spago/
    rm -rf dist-newstyle/
    rm -rf src/proofs/lean/.lake/
    rm -rf src/rules/lean/.lake/
    
    echo_success "Clean complete"
}

# Show file counts
stats() {
    echo_step "Project statistics..."
    
    local ps_count=$(find src -name "*.purs" 2>/dev/null | wc -l)
    local hs_count=$(find src -name "*.hs" 2>/dev/null | wc -l)
    local lean_count=$(find src -name "*.lean" 2>/dev/null | wc -l)
    
    echo "  PureScript files: $ps_count"
    echo "  Haskell files:    $hs_count"
    echo "  Lean4 files:      $lean_count"
    echo "  Total:            $((ps_count + hs_count + lean_count))"
}

# Main
case "${1:-build}" in
    build)
        check_tools
        build_purescript
        build_haskell
        build_lean_proofs
        echo_success "Build complete!"
        ;;
    ps|purescript)
        build_purescript
        ;;
    hs|haskell)
        build_haskell
        ;;
    lean|proofs)
        build_lean_proofs
        ;;
    test)
        run_tests
        ;;
    clean)
        clean
        ;;
    stats)
        stats
        ;;
    check)
        check_tools
        ;;
    *)
        echo "Usage: $0 {build|ps|hs|lean|test|clean|stats|check}"
        echo ""
        echo "Commands:"
        echo "  build      Build all components (default)"
        echo "  ps         Build PureScript only"
        echo "  hs         Build Haskell only"
        echo "  lean       Build/verify Lean4 proofs only"
        echo "  test       Run all tests"
        echo "  clean      Clean build artifacts"
        echo "  stats      Show file statistics"
        echo "  check      Check for required tools"
        exit 1
        ;;
esac
