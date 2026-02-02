# Runtime Library: C++23 → React Bridge

## Overview

Runtime library that bridges C++23 code to React runtime, handling:
- Memory management
- Event handling
- State management
- Component lifecycle

## Architecture

1. **WASM Module** - C++23 compiled to WebAssembly
2. **JavaScript Bridge** - WASM ↔ React interface
3. **React Hooks** - React integration layer
4. **Type System** - TypeScript type definitions

## Components

- `wasm_bridge.cpp` - C++23 WASM exports
- `react_bridge.ts` - JavaScript/TypeScript bridge
- `react_hooks.tsx` - React hooks for C++ components
- `types.ts` - TypeScript type definitions
