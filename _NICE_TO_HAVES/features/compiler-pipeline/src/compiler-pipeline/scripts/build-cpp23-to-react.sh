#!/usr/bin/env bash
set -euo pipefail

# LLVM_CLANG_INCLUDE is set by Nix build environment
# This script is called from flake.nix build-phase
clang++ -std=c++23 -O2 -o cpp23-to-react \
  -I"$LLVM_CLANG_INCLUDE" \
  -I"$LLVM_CLANG_INCLUDE/clang-c" \
  src/main.cpp \
  src/ReactGenerator.cpp \
  src/RadixBinder.cpp \
  src/TailwindGenerator.cpp \
  src/Cpp23Parser.cpp \
  src/NexusIntegration.cpp \
  -lclang
