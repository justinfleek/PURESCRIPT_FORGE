# Compiler Pipeline: Haskell/PureScript/Lean4 → C++23 → React/Tailwind/Radix

## Architecture

```
┌─────────────────┐
│  PureScript     │
│  Haskell        │  ──┐
│  Lean4          │    │
└─────────────────┘    │
                       │
                       ▼
            ┌──────────────────┐
            │  AST Parsers     │
            │  - PureScript    │
            │  - GHC Core      │
            │  - Lean IR       │
            └──────────────────┘
                       │
                       ▼
            ┌──────────────────┐
            │  C++23 Generator │
            │  - Type mapping  │
            │  - Code gen      │
            │  - Runtime lib   │
            └──────────────────┘
                       │
                       ▼
            ┌──────────────────┐
            │  C++23 → React   │
            │  - Component gen │
            │  - TypeScript    │
            │  - Radix bindings│
            │  - Tailwind      │
            └──────────────────┘
                       │
                       ▼
            ┌──────────────────┐
            │  React Components│
            │  + Tailwind CSS  │
            │  + Radix UI      │
            └──────────────────┘
```

## Components

1. **Language Parsers** - Parse source code to AST
2. **C++23 Generator** - Generate C++23 from AST
3. **React Generator** - Generate React/TypeScript from C++23
4. **Runtime Library** - Bridge C++23 to React runtime
5. **Build System** - Nix/Buck2 integration
