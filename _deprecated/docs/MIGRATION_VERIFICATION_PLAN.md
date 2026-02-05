# Migration Verification Plan

## Current Gap

**What I've been doing:**
- PureScript implementation migration ✅
- Basic type safety ✅

**What's missing:**
- Lean4 proofs for migrated code ❌
- Graded monads for resource tracking ❌
- Co-effect equations ❌

## Required Pattern

For each migrated module, we need:

### 1. PureScript Implementation
```
packages/console/app/src/routes/auth/Index.purs
```
- Pure PureScript (no unnecessary FFI)
- Proper types
- Deterministic logic

### 2. Lean4 Proofs
```
src/console-lean/Console/App/Routes/Auth/Index.lean
```
- Theorems proving correctness
- Invariant preservation
- Safety properties

### 3. Graded Monads (where applicable)
For resource-tracking operations:
- Database access
- Network requests
- File operations

### 4. Co-effect Equations (where applicable)
For protocol-level verification:
- API route handlers
- State transitions
- Permission checks

## Verification Checklist

For each migrated file:

- [ ] PureScript implementation complete
- [ ] Lean4 proofs created
- [ ] Proofs check (`lake build`)
- [ ] Graded monads used (if resource tracking needed)
- [ ] Co-effect equations defined (if protocol verification needed)
- [ ] Documentation updated with proof references

## Next Steps

1. Create Lean4 proofs for all migrated routes
2. Add graded monads for database operations
3. Add co-effect equations for API handlers
4. Verify all proofs check
