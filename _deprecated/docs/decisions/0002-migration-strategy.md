# ADR 0002: OpenCode Migration Strategy

## Status
Proposed

## Context

We need to migrate `opencode-dev` (TypeScript/Bun) to match `trtllm-serve-main` standards:
- Type safety (PureScript/Haskell/Lean4)
- Nix-based reproducible builds
- Strict type checking
- Complete file reading protocol
- No banned constructs
- Proven correctness

## Decision

**Incremental migration strategy:**

1. **Phase 1: Foundation** (Current)
   - Set up Nix flake for opencode-dev
   - Add PureScript/Haskell/Lean4 tooling
   - Create rule implementations
   - Set up CI/CD

2. **Phase 2: Type Safety Layer**
   - Add PureScript type definitions for core types
   - Create Haskell validation tools
   - Add Lean4 proofs for critical invariants
   - Keep TypeScript for UI (gradual migration)

3. **Phase 3: Core Logic Migration**
   - Migrate core business logic to PureScript
   - Performance-critical paths to Haskell
   - Add proofs for critical operations

4. **Phase 4: Build System**
   - Migrate to Nix-based builds
   - Remove Bun-specific dependencies
   - Ensure reproducibility

5. **Phase 5: Complete Migration**
   - All logic in PureScript/Haskell
   - All proofs in Lean4
   - TypeScript only for UI bindings

## Consequences

### Positive
- Incremental migration reduces risk
- Can verify each phase
- Maintains working system throughout

### Negative
- Longer migration timeline
- Need to maintain both systems temporarily
- More complex build system

### Mitigation
- Each phase has clear success criteria
- Automated verification at each step
- Rollback plan for each phase

## Alternatives Considered

1. **Big bang migration**: Rejected - too risky, breaks working system
2. **No migration**: Rejected - doesn't meet standards
3. **TypeScript-only improvements**: Rejected - doesn't meet PureScript/Haskell/Lean4 requirement

## Success Criteria

- [ ] Nix flake builds opencode-dev
- [ ] Core types have PureScript definitions
- [ ] Critical operations have Lean4 proofs
- [ ] CI verifies all proofs
- [ ] No banned constructs in codebase
- [ ] All tests pass

## Next Steps

1. Create Nix flake for opencode-dev
2. Identify core types to migrate first
3. Create PureScript type definitions
4. Add Lean4 proofs for critical operations
