# Fix All Axioms - Strong Proofs Only

## Principle

**NO `sorry`**  
**NO `axiom`**  
**STRONG PROOFS ONLY**

## Current Axioms to Fix

### 1. `src/rules-lean/src/Bridge/Security/Invariants.lean`
- [ ] `encryption_roundtrip_axiom` → Prove from string manipulation
- [ ] `encryption_security_axiom` → Prove from endsWith uniqueness  
- [ ] `secrets_encryption_axiom` → Fix model or prove from implementation
- [ ] `security_headers_axiom` → Make conditional or prove from middleware

### 2. `src/rules-lean/src/Bridge/Auth/Properties.lean`
- [ ] `role_hierarchy_implies_permissions` → Define explicit inheritance rules
- [ ] `validateToken_checks_expiration` → Implement complete validateToken

### 3. `src/rules-lean/src/Bridge/Backup/Properties.lean`
- [ ] `restore_correctness_axiom` → Prove from backup/restore implementation

### 4. `src/rules-lean/src/Bridge/Error/Correctness.lean`
- [ ] `retry_termination_axiom` → Prove termination from retry logic
- [ ] `error_recovery_axiom` → Prove from recovery strategy implementation

## Required String Lemmas

Create `src/rules-lean/src/Bridge/Security/StringLemmas.lean` with:

1. `append_startsWith` - Proven ✅
2. `append_endsWith` - Proven ✅  
3. `drop_append` - Needs Mathlib lemmas
4. `dropRight_append` - Needs Mathlib lemmas
5. `endsWith_unique_length` - Needs proof
6. `append_suffix_eq` - Needs cancellation lemma

## Approach

1. **Use Mathlib string lemmas** where available
2. **Prove missing lemmas** from first principles
3. **Fix model definitions** if they prevent proofs
4. **Make conditional** if proof requires runtime assumptions

## Status

- [ ] String lemmas file created
- [ ] All string lemmas proven
- [ ] Encryption proofs fixed
- [ ] Auth proofs fixed
- [ ] Backup proofs fixed
- [ ] Error proofs fixed
- [ ] All proofs verify (`lake build`)
