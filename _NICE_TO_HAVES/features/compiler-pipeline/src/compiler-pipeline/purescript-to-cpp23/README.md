# PureScript → C++23 Compiler

## Overview

Compiles PureScript source code to C++23, preserving type safety and functional programming patterns.

## Type Mapping

| PureScript | C++23 |
|------------|-------|
| `Int` | `std::int64_t` |
| `Number` | `double` |
| `String` | `std::string` |
| `Boolean` | `bool` |
| `Array a` | `std::vector<T>` |
| `Maybe a` | `std::optional<T>` |
| `Either a b` | `std::variant<A, B>` |
| `Record` | `struct` |
| `Effect` | `std::function<void()>` |
| `Aff` | `std::future<T>` |
| Type classes | C++20 concepts |
| Higher-kinded types | Template template parameters |

## Architecture

1. **Parser** - Parse PureScript source to AST
2. **Type Checker** - Resolve types and type classes
3. **C++23 Generator** - Generate C++23 code
4. **Runtime Library** - PureScript runtime in C++23
