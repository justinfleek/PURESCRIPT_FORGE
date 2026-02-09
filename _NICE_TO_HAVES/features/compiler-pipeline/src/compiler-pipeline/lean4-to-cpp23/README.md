# Lean4 → C++23 Compiler

## Overview

Compiles Lean4 source code (via Lean IR) to C++23, preserving dependent types and proof information.

## Architecture

1. **Lean IR Parser** - Extract Lean IR from compiled Lean4
2. **IR → C++23 Translator** - Translate Lean IR to C++23
3. **Proof Preservation** - Maintain proof information in C++23

## Type Mapping

| Lean4 | C++23 |
|-------|-------|
| `Nat` | `std::uint64_t` |
| `Int` | `std::int64_t` |
| `String` | `std::string` |
| `Bool` | `bool` |
| `List a` | `std::vector<T>` |
| `Option a` | `std::optional<T>` |
| `Prod a b` | `std::pair<A, B>` |
| Dependent types | Template specialization |
| Proofs | `constexpr` functions |
