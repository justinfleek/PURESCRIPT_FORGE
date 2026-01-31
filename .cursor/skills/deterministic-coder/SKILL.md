---
name: deterministic-coder
description: MANDATORY for ALL code modifications. Ensures complete file reading, dependency tracing, type safety, and verification before any code changes.
---

# Deterministic Coder

**MANDATORY for ALL code operations.**

## Process

1. **Load skill** (you're reading this)
2. **Read ALL affected files completely** (no grep, no partial)
   - If file >500 lines, chunk into segments
   - Read ALL chunks sequentially
3. **Trace dependency graph**
   - Upstream: Module ← Imports ← Transitive Imports
   - Downstream: Module → Exports → Consumers → Transitive Consumers
4. **Perform code modifications**
   - Fix ALL instances across codebase (not just one file)
   - No banned constructs
   - Explicit types at function boundaries
5. **Validate**
   - Type checks pass (`npx tsc --noEmit` or equivalent)
   - Lint passes (`npx biome check` or equivalent)
   - Tests pass
6. **Update MASTER documentation**
   - Record what changed, why, dependencies affected
7. **Clean workspace**
   - Remove generated artifacts
   - Clear test caches

## Verification Checklist

Before completion:
- [ ] All files read completely (no grep, no partial)
- [ ] Dependency graph traced up and down
- [ ] ALL instances fixed across codebase
- [ ] No banned constructs present
- [ ] Types explicit at function boundaries
- [ ] Type checks pass
- [ ] Lint passes
- [ ] Tests pass
- [ ] MASTER.md updated
- [ ] Workspace clean
- [ ] No technical debt introduced

If any box unchecked: task incomplete.
