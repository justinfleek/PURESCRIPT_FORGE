#!/usr/bin/env bash
set -euo pipefail

echo "=== Full Compiler Pipeline Test Suite ==="
nix run .#compiler-pipeline-test
nix run .#compiler-pipeline-test-integration
echo "=== All tests passed ==="
