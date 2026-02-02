#!/usr/bin/env bash
set -euo pipefail

echo "=== Running Compiler Pipeline Tests ==="
cd src/compiler-pipeline/purescript-to-cpp23
cabal test parser-tests
cabal test generator-tests
cabal test typechecker-tests
echo "=== All tests passed ==="
