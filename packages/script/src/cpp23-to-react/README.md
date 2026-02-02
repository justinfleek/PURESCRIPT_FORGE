# C++23 → React/TypeScript Generator

## Overview

Generates React components with TypeScript types, Radix UI components, and Tailwind CSS from C++23 code.

## Architecture

1. **C++23 Parser** - Parse C++23 AST (using Clang libTooling)
2. **Component Analyzer** - Identify UI components and their props
3. **React Generator** - Generate React/TypeScript components
4. **Radix Binder** - Map C++ types to Radix UI components
5. **Tailwind Generator** - Generate Tailwind classes from C++ styling

## Type Mapping

| C++23 | React/TypeScript |
|-------|------------------|
| `struct` | `interface` |
| `std::string` | `string` |
| `std::vector<T>` | `T[]` |
| `std::optional<T>` | `T | null` |
| `std::variant<A, B>` | `A \| B` |
| `std::function<T(U)>` | `(u: U) => T` |
| Component struct | React component |
