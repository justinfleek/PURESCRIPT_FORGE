# Migration Checklist - TypeScript to PureScript/Haskell/Lean4

**Last Updated:** 2026-02-03
**Status:** Active Migration

---

## SINGLE SOURCE OF TRUTH

| Purpose | Location | Status |
|---------|----------|--------|
| **TypeScript Reference** | `_OTHER/opencode-original/` | CANONICAL SOURCE |
| **PureScript Target** | `packages/` | Active migration |
| **PS/HS/Lean4 Modules** | `src/*-ps/`, `src/*-hs/`, `src/*-lean/` | Additional services |
| **Archived** | `_archived/` | Deprecated duplicates |

### NEVER use these as source:
- `opencode-dev/` - ARCHIVED (was duplicate with additions now merged)
- Any other `*-original` or `*-dev` directories

---

## PRE-SESSION CHECKLIST

Before starting any migration work:

- [ ] **1. Verify source path**: `_OTHER/opencode-original/packages/`
- [ ] **2. Load skill**: Run `skill deterministic-coder`
- [ ] **3. Check current state**: `git status && git log -3 --oneline`
- [ ] **4. Read this checklist**: Confirm you understand the workflow
- [ ] **5. Read MIGRATION_TODO.md**: Check what's already done

---

## FILE MIGRATION WORKFLOW

For EACH TypeScript file being migrated:

### Step 1: Read Completely
```
- [ ] Read the ENTIRE TypeScript source file
- [ ] Identify all imports and dependencies
- [ ] Note any browser/Node APIs used (FFI needed)
- [ ] Understand the complete behavior
```

### Step 2: Trace Dependencies
```
- [ ] List upstream dependencies (what this file imports)
- [ ] List downstream consumers (what imports this file)
- [ ] Verify upstream PS modules exist
- [ ] Plan any cascading changes needed
```

### Step 3: Create PureScript Module
```
- [ ] Create .purs file with proper module declaration
- [ ] Add explicit type signatures for ALL exports
- [ ] NO banned constructs (Nullable, toMaybe, unsafeCoerce, etc.)
- [ ] Create .js FFI file if browser APIs used
```

### Step 4: Verify
```
- [ ] Module compiles (spago build)
- [ ] Types are correct and complete
- [ ] FFI signatures match JS exports
- [ ] Update module's spago.yaml if new dependency
```

### Step 5: Document
```
- [ ] Update MIGRATION_TODO.md with completion
- [ ] Mark file as DONE in tracking table
- [ ] Note any issues or decisions made
```

---

## MIGRATION STATUS

### Completed Packages
| Package | TS Files | PS Files | Status |
|---------|----------|----------|--------|
| opencode | 312 | 325 | COMPLETE |
| enterprise | 18 | 2+ | COMPLETE |
| util | 12 | 11 | COMPLETE |
| plugin | 6 | 8 | COMPLETE |
| app | 128 | 83 | 64% |

### In Progress
| Package | TS Files | PS Files | Progress |
|---------|----------|----------|----------|
| ui | 87 | 51 | 58% |
| console | 156 | 3 | 2% |

### Not Started
| Package | TS Files | Priority | Notes |
|---------|----------|----------|-------|
| sdk | 40 | Medium | May keep as TS for npm |
| desktop | 26 | Low | Electron-specific |
| web | 16 | Low | SST/AWS deployment |
| slack | 2 | Low | Integration |
| containers | 1 | Low | Docker config |
| function | 2 | Low | Lambda handlers |

---

## PACKAGE DIRECTORY STRUCTURE

### TypeScript Source (Reference)
```
_OTHER/opencode-original/packages/
├── app/           # 128 files - Main application
├── console/       # 156 files - Web console
├── desktop/       # 26 files  - Desktop app
├── enterprise/    # 18 files  - Enterprise features
├── opencode/      # 312 files - Core CLI/TUI
├── plugin/        # 6 files   - Plugin system
├── sdk/           # 40 files  - Client SDK
├── ui/            # 87 files  - UI components
├── util/          # 12 files  - Utilities
└── web/           # 16 files  - Web deployment
```

### PureScript Target
```
packages/
├── app/src/       # Halogen components, contexts, hooks
├── console/src/   # Web console (todo)
├── enterprise/src/# Enterprise (complete)
├── forge/src/     # NEW - Build system
├── opencode/src/  # Core (complete)
├── plugin/src/    # Plugin (complete)
├── ui/src/        # UI components (in progress)
└── util/src/      # Utils (complete)
```

### Service Modules (src/)
```
src/
├── *-ps/          # PureScript services
├── *-hs/          # Haskell validation/processing
└── *-lean/        # Lean4 proofs
```

---

## BANNED CONSTRUCTS

These are NEVER allowed in migrated code:

### PureScript
- `Nullable` - Use `Maybe`
- `toMaybe` - Pattern match explicitly
- `unsafeCoerce` - Use proper types
- `foreign import data` without `.js` file
- Incomplete pattern matches

### Haskell
- `undefined` - Handle all cases
- `error` in pure code - Use `Either`/`Maybe`
- Partial functions (head, tail, !!)
- `unsafePerformIO`

### Lean4
- `sorry` - Complete all proofs
- `axiom` without justification
- `native_decide` on non-trivial propositions

---

## FFI GUIDELINES

When TypeScript uses browser/Node APIs:

1. **Create companion .js file**
```javascript
// Module.js
export const functionName = (arg) => {
  // implementation
};
```

2. **Match with foreign import**
```purescript
-- Module.purs
foreign import functionName :: ArgType -> Effect ReturnType
```

3. **Common FFI patterns**
- DOM operations → Effect
- Async operations → Aff
- Callbacks → EffectFn
- Mutable state → Ref

---

## BUILD VERIFICATION

After completing a package:

```bash
# Build specific package
cd packages/<name>
spago build

# Run tests if present
spago test

# Type check
spago check

# Full workspace build
nix build .#all-packages
```

---

## GIT WORKFLOW

```bash
# After each file/module completion
git add packages/<modified>
git commit -m "Migrate <package>/<module>: <description>"

# After completing a package
git add .
git commit -m "Complete <package> migration: <count> modules"

# Push regularly
git push origin main
```

---

## QUALITY GATES

Before marking any file as complete:

- [ ] No TypeScript remains in target directory
- [ ] All types are explicit (no inference at boundaries)
- [ ] No banned constructs used
- [ ] FFI files have matching exports
- [ ] Compiles without warnings
- [ ] Documented in MIGRATION_TODO.md

---

## COMMON ISSUES & SOLUTIONS

### Issue: "Module not found"
**Solution**: Check spago.yaml has the dependency listed

### Issue: "FFI function not found"
**Solution**: Ensure .js file exports match foreign import names

### Issue: "Type mismatch in FFI"
**Solution**: Verify Effect/Aff wrappers are correct

### Issue: "Circular dependency"
**Solution**: Extract shared types to separate module

---

## SESSION END CHECKLIST

Before ending a session:

- [ ] All work committed to git
- [ ] MIGRATION_TODO.md updated
- [ ] No partial migrations (complete file or revert)
- [ ] Build passes (`spago build`)
- [ ] Push to remote

---

## CONTACTS & REFERENCES

- OpenCode docs: https://opencode.ai/docs
- PureScript: https://pursuit.purescript.org
- Haskell: https://hoogle.haskell.org
- Lean4: https://leanprover.github.io

---

*This checklist is the authoritative workflow document for migration sessions.*
