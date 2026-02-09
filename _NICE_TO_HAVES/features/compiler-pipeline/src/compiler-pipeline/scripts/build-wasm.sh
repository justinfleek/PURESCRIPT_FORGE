#!/usr/bin/env bash
set -euo pipefail

emcc -std=c++23 -O2 \
  -s WASM=1 \
  -s EXPORTED_FUNCTIONS='["_registerCppComponent","_createCppComponent"]' \
  -s EXPORTED_RUNTIME_METHODS='["ccall","cwrap"]' \
  -o wasm_bridge.js \
  src/wasm_bridge.cpp
