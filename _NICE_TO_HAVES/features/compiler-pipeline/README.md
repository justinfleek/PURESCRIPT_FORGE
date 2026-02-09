# Compiler Pipeline

PureScript → C++23 → React compilation pipeline.

## Components
- `src/compiler-pipeline/`
  - purescript-to-cpp23 - PS to C++ compiler (Haskell)
  - cpp23-to-react - C++ to React generator
  - runtime - WASM runtime

## Integration
1. Copy src/compiler-pipeline to main src/
2. Add packages to flake.nix
3. Requires LLVM 18+ and Emscripten
