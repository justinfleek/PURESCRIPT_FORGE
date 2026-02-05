# Proof Fixes Required - Remove All Axioms

## Current State

**Files with `axiom` declarations:**
1. `src/rules-lean/src/Bridge/Security/Invariants.lean` - 4 axioms
2. `src/rules-lean/src/Bridge/Auth/Properties.lean` - 2 axioms  
3. `src/rules-lean/src/Bridge/Backup/Properties.lean` - 1 axiom
4. `src/rules-lean/src/Bridge/Error/Correctness.lean` - 2 axioms

## Required Fixes

### 1. Encryption Roundtrip (`Bridge.Security.Invariants.lean`)

**Current (WRONG):**
```lean
axiom encryption_roundtrip_axiom (plaintext : String) (key : String) :
  decrypt (encrypt plaintext key) key = some plaintext
```

**Required (STRONG PROOF):**
```lean
theorem encryption_roundtrip_property (plaintext : String) (key : String) :
  decrypt (encrypt plaintext key) key = some plaintext := by
  -- Prove from definitions:
  -- encrypt(plaintext, key) = "encrypted_" ++ plaintext ++ "_" ++ key
  -- decrypt checks: startsWith "encrypted_" && endsWith ("_" ++ key)
  -- Both are true by construction
  -- drop 10 removes "encrypted_" (10 chars)
  -- dropRight (key.length + 1) removes "_" ++ key
  -- Result is plaintext
  -- Requires string manipulation lemmas for drop/dropRight/append
```

**String Lemmas Needed:**
- `(s1 ++ s2).drop s1.length = s2`
- `(s1 ++ s2).dropRight s2.length = s1`
- `(s1 ++ s2).endsWith s2 = true`

### 2. Encryption Security (`Bridge.Security.Invariants.lean`)

**Current (WRONG):**
```lean
axiom encryption_security_axiom (plaintext : String) (key1 key2 : String) :
  (key1 ≠ key2) → (decrypt (encrypt plaintext key1) key2 = none)
```

**Required (STRONG PROOF):**
- Prove that if key1 ≠ key2, then endsWith check fails
- Requires: `(s.endsWith s1) ∧ (s.endsWith s2) → s1 = s2`

### 3. Secrets Encryption (`Bridge.Security.Invariants.lean`)

**Current (WRONG):**
```lean
axiom secrets_encryption_axiom (secret : String) (masterKey : String) :
  (storeSecret secret masterKey) →
  (getStoredSecret secret = encrypt secret masterKey)
```

**Required (STRONG PROOF):**
- This is actually provable directly since `getStoredSecret` uses hardcoded "default_key"
- Need to prove: `encrypt secret "default_key" = encrypt secret masterKey` is false unless masterKey = "default_key"
- Or change the model to use masterKey properly

### 4. Security Headers (`Bridge.Security.Invariants.lean`)

**Current (WRONG):**
```lean
axiom security_headers_axiom (response : HttpResponse) :
  hasSecurityHeaders response = true
```

**Required (STRONG PROOF):**
- This cannot be proven without assuming middleware behavior
- **Solution:** Change to conditional: "IF middleware adds headers, THEN hasSecurityHeaders"
- Or prove: "hasSecurityHeaders (addSecurityHeaders response) = true"

### 5. Role Hierarchy (`Bridge.Auth/Properties.lean`)

**Current (WRONG):**
```lean
axiom role_hierarchy_implies_permissions ...
```

**Required (STRONG PROOF):**
- Define explicit permission inheritance rules
- Prove from role definitions, not axiom

### 6. Token Expiration (`Bridge.Auth/Properties.lean`)

**Current (WRONG):**
```lean
axiom validateToken_checks_expiration ...
```

**Required (STRONG PROOF):**
- Implement complete validateToken that checks expiration
- Prove from implementation

## Action Plan

1. **Create string manipulation lemmas** (Mathlib or custom)
2. **Fix encryption proofs** using lemmas
3. **Fix auth proofs** by implementing complete functions
4. **Fix security headers** by making conditional
5. **Fix backup/error proofs** similarly

## Status

- [ ] String manipulation lemmas created
- [ ] Encryption proofs fixed
- [ ] Auth proofs fixed  
- [ ] Security headers fixed
- [ ] Backup proofs fixed
- [ ] Error proofs fixed
- [ ] All proofs verified (`lake build`)
