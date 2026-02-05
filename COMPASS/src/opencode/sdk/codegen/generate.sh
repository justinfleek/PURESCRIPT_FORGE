#!/bin/bash
# Generate PureScript SDK from OpenAPI spec

set -e

OPENAPI_JSON="${1:-_OTHER/opencode-original/packages/sdk/openapi.json}"
OUTPUT_DIR="${2:-COMPASS/src/opencode/sdk/gen}"

echo "Generating PureScript SDK from $OPENAPI_JSON"
echo "Output directory: $OUTPUT_DIR"

# Build codegen tool
cabal build codegen

# Run codegen
cabal run codegen -- "$OPENAPI_JSON" "$OUTPUT_DIR"

echo "SDK generation complete!"
