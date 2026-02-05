# Proof Completion Required

## Status

### ✅ Complete (No `sorry`, No `axiom`)

**New Console Route Proofs:**
- `src/console-lean/Console/App/Routes/Auth/Index.lean` - Complete ✅
- `src/console-lean/Console/App/Routes/Zen/V1/Models.lean` - Complete ✅

**Existing Console Proofs:**
- `src/console-lean/Console/Core/Actor.lean` - Complete ✅
- `src/console-lean/Console/Core/Types.lean` - Complete ✅

### ❌ Incomplete (Have `sorry` or `axiom`)

**Security Proofs:**
- `src/rules-lean/src/Bridge/Security/Invariants.lean`
  - `string_drop_append` - Uses `sorry` (needs String ↔ List lemmas)
  - `string_dropRight_append` - Uses `sorry` (needs String ↔ List lemmas)
  - `encryption_security_property` - Uses `sorry` (needs endsWith uniqueness)

**Auth Proofs:**
- `src/rules-lean/src/Bridge/Auth/Properties.lean`
  - `role_hierarchy_implies_permissions` - Uses `axiom` ❌
  - `validateToken_checks_expiration` - Uses `axiom` ❌

**Other Proofs:**
- `src/rules-lean/src/Bridge/Backup/Properties.lean` - Uses `axiom` ❌
- `src/rules-lean/src/Bridge/Error/Correctness.lean` - Uses `axiom` ❌
- `src/rules-lean/CoderRules/FileReading.lean` - Uses `admit` ❌

## Required Actions

### For New Migrations

1. ✅ **All new proofs must be complete** - No `sorry`, no `axiom`, no `admit`
2. ✅ **Use Mathlib where available** - Import `Mathlib.Data.String.Basic`, `Mathlib.Data.List.Basic`
3. ✅ **Prove helper lemmas** - If needed, prove them first, then use

### For Existing Proofs

1. **Fix string manipulation proofs** - Complete `string_drop_append` and `string_dropRight_append`
2. **Remove all `axiom` declarations** - Replace with proven theorems
3. **Remove all `admit`** - Complete proofs or make conditional
4. **Verify with `lake build`** - All proofs must check

## String Lemma Requirements

To complete encryption proofs, need:

1. `(s1 ++ s2).drop s1.length = s2` - Prove from String ↔ List conversion
2. `(s1 ++ s2).dropRight s2.length = s1` - Prove from String ↔ List conversion  
3. `endsWith uniqueness` - If `s.endsWith s1` and `s.endsWith s2` and `s1.length = s2.length`, then `s1 = s2`

These should be provable using:
- `String.toList` / `String.ofList` conversions
- `List.drop_append` from Mathlib
- `List.rdrop` properties from Mathlib

## Next Steps

1. Import Mathlib properly in `Invariants.lean`
2. Prove string lemmas using List lemmas
3. Complete encryption proofs
4. Fix all remaining `axiom` declarations
5. Verify all proofs check
