# Advanced Features

Phase 3: Advanced Features implementation for the compiler pipeline.

## Components

### 1. Higher-Kinded Types (HKT)

**File**: `HigherKindedTypes.hs`

Supports higher-kinded types (types parameterized by types) with:
- HKT extraction from Core
- C++23 template generation for HKTs
- C++20 concepts for HKT constraints
- Common HKT patterns (Functor, Applicative, Monad, Traversable)

**Usage**:
```haskell
-- Extract HKTs from Core bindings
hkts <- extractHKTs coreBindings

-- Generate C++23 templates
cppCode <- mapM generateHKTTemplate hkts
```

### 2. Type Class Instance Resolution

**File**: `TypeClassResolution.hs`

Implements type class instance resolution with:
- Constraint solving algorithm
- Instance selection
- Resolution context management
- C++23 concept specialization generation

**Usage**:
```haskell
-- Solve constraints
result <- solveConstraints constraints availableInstances

-- Generate resolution code
cppCode <- generateInstanceResolution resolvedContext
```

### 3. Effect System Translation

**File**: `EffectSystem.hs`

Translates effect systems to C++23:
- Pure computations
- IO effects
- Exception handling (Except)
- State management
- Reader/Writer effects
- Async effects
- Effect rows (PureScript style)

**Supported Effects**:
- `EffectPure` → Direct value
- `EffectIO` → `IO<T>` monad
- `EffectExcept` → `Except<T>` with error handling
- `EffectState` → `State<T, S>` with state threading
- `EffectReader` → `Reader<T, E>` with environment
- `EffectWriter` → `Writer<T, L>` with logging
- `EffectAsync` → `std::future<T>`

### 4. Async/Await Support

**File**: `AsyncAwait.hs`

C++20 coroutines for async/await:
- Coroutine promise types
- Awaitable types
- Task type for async operations
- `async` function generator
- `await` helper

**Usage**:
```cpp
Task<int> compute() {
  co_return 42;
}

int result = await(compute());
```

### 5. Pattern Matching Optimization

**File**: `PatternOptimization.hs`

Optimizes pattern matching:
- Alternative reordering (DEFAULT last, literals before constructors)
- Pattern matching optimization passes
- C++23 `std::visit` generation with optimal ordering

**Optimizations**:
- Reorder alternatives for better matching performance
- Optimize nested pattern matches
- Generate efficient C++23 variant matching

### 6. Tail Call Optimization

**File**: `TailCallOptimization.hs`

Converts tail-recursive functions to loops:
- Tail call detection
- Loop conversion
- Stack-safe recursion elimination

**Usage**:
```haskell
-- Detect and optimize tail calls
optimized <- optimizeTailCalls expr

-- Generate C++23 loop
cppCode <- generateTailCallLoop optimized
```

## Integration

All advanced features integrate with:
- PureScript compiler (`purescript-to-cpp23`)
- Haskell compiler (`haskell-to-cpp23`)
- Lean4 compiler (`lean4-to-cpp23`)

## Status

✅ **All Phase 3 components implemented**

Ready for integration testing and optimization passes.
