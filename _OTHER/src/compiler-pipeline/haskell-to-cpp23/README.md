# Haskell → C++23 Compiler

## Overview

Compiles Haskell source code (via GHC Core) to C++23, preserving type safety and functional programming patterns.

## Architecture

1. **GHC Core Parser** - Extract GHC Core IR from compiled Haskell
2. **Core → C++23 Translator** - Translate Core to C++23
3. **Runtime Library** - Haskell runtime in C++23

## Type Mapping

| Haskell | C++23 |
|---------|-------|
| `Int` | `std::int64_t` |
| `Double` | `double` |
| `String` | `std::string` |
| `Bool` | `bool` |
| `[a]` | `std::vector<T>` |
| `Maybe a` | `std::optional<T>` |
| `Either a b` | `std::variant<A, B>` |
| `IO a` | `std::future<T>` |
| Type classes | C++20 concepts |
| GADTs | `std::variant` with type tags |
