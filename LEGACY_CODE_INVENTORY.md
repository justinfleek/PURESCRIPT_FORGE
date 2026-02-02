
# Legacy Code Inventory - Code That Shouldn't Exist

**Date:** 2026-01-31  
**Status:** ✅ **MOVED TO `_deprecated/`** (not pushed to git)

---

## ✅ DEPRECATED: Moved to `_deprecated/` Directory

**Note:** The `_deprecated/` directory is excluded from git (see `.gitignore`).  
These directories are kept locally for reference but will not be pushed to the repository.

### 1. **`_deprecated/src/bridge-server/`** - TypeScript Bridge Server ✅ MOVED
**Status:** Legacy - Moved to `_deprecated/src/bridge-server/`  
**Reason:** Violates language stack (PureScript/Haskell/Lean4 only)  
**Replacement:** `src/bridge-server-ps/` (PureScript implementation)  
**Files:** 34 TypeScript files + tests

**Contents:**
- `_deprecated/src/bridge-server/src/` - All TypeScript source files
- `_deprecated/src/bridge-server/test/` - All TypeScript tests
- `_deprecated/src/bridge-server/package.json` - TypeScript package config
- `_deprecated/src/bridge-server/tsconfig.json` - TypeScript config

**Action:** ✅ MOVED - Directory preserved locally but excluded from git

---

### 2. **`src/opencode-plugin/`** - TypeScript OpenCode Plugin ✅ ACTIVE
**Status:** Active - Required for OpenCode plugin system  
**Reason:** OpenCode loads plugins from npm/local files - this is the plugin that gets loaded  
**Note:** PureScript version (`src/opencode-plugin-ps/`) compiles to JavaScript, but this TypeScript version is needed for the plugin system to work  
**Files:** 4 TypeScript files

**Contents:**
- `src/opencode-plugin/src/bridge-client.ts`
- `src/opencode-plugin/src/index.ts`
- `src/opencode-plugin/package.json`
- `src/opencode-plugin/tsconfig.json`

**Action:** ✅ KEEP - Required for plugin system functionality

---

## ⚠️ MIGRATION IN PROGRESS: TypeScript Code Being Migrated

### 3. **`opencode-dev/`** - Entire TypeScript/Bun Project ⏳ MIGRATING
**Status:** Migration target - Being migrated to PureScript/Haskell/Lean4  
**Reason:** Violates language stack, but migration in progress  
**Files:** ~2000+ TypeScript/TSX files

**Current State:**
- TypeScript/Bun codebase
- Being migrated per `docs/MIGRATION.md`
- Should eventually be PureScript/Haskell/Lean4 only

**Action:** Continue migration, remove when complete

**Note:** This is a large migration project, not immediate deletion

---

## 🔍 OTHER LEGACY CODE

### 4. **`src/compiler-pipeline/runtime/src/react_bridge.ts`** ⚠️ CHECK
**Status:** TypeScript runtime bridge  
**Reason:** May be needed for React integration, but violates language stack  
**Files:**
- `src/compiler-pipeline/runtime/src/react_bridge.ts`
- `src/compiler-pipeline/runtime/src/react_hooks.tsx`
- `src/compiler-pipeline/runtime/src/types.ts`

**Action:** Verify if this is needed for PureScript→React compilation, or if it should be migrated

---

### 5. **Python Code in `NEXUS/`** ⚠️ CHECK STATUS
**Status:** May be legacy if PureScript versions exist  
**Reason:** Language stack says PureScript/Haskell/Lean4 only  

**Directories to Check:**
- `NEXUS/agent-orchestrator/` (Python)
- `NEXUS/network-graph/` (Python) - Has `network-graph-hs/` and `network-graph-ps/`
- `NEXUS/agent-social/` (Python) - Has `agent-social-ps/`
- `NEXUS/web-search-agent/` (Python)
- `NEXUS/content-extraction-agent/` (Python)
- `NEXUS/network-formation-agent/` (Python)
- `NEXUS/semantic-memory/` (Python) - Has `semantic-memory-distributed-hs/` and `semantic-memory-distributed-ps/`

**Action:** Check if Python versions are legacy or still needed for FFI

---

### 6. **`src/voice-engine/`** - Python Voice Engine ⚠️ CHECK STATUS
**Status:** Python implementation  
**Reason:** May be acceptable if it's FFI-only (like STRAYLIGHT Python)  
**Files:** Python voice engine code

**Action:** Verify if this is FFI-only (acceptable) or contains business logic (should migrate)

---

## 📊 SUMMARY

| Category | Count | Status | Action |
|----------|-------|--------|--------|
| **TypeScript Directories (DEPRECATED)** | 1 | ✅ Moved | `bridge-server` moved to `_deprecated/` |
| **TypeScript Plugin (ACTIVE)** | 1 | ✅ Active | `opencode-plugin` required for plugin system |
| **TypeScript Files (Migration)** | ~2000+ | ⏳ In Progress | Continue migration |
| **Python (Check Status)** | ~10 dirs | ⚠️ Verify | Check if legacy or FFI-only |

---

## 🎯 IMMEDIATE ACTIONS

### Priority 1: ✅ COMPLETED
1. ✅ **`src/bridge-server/`** - Moved to `_deprecated/src/bridge-server/`
2. ✅ **`src/opencode-plugin/`** - ✅ RESTORED - Required for plugin system
3. ✅ Created `.gitignore` to exclude `_deprecated/` from git

**Status:** Legacy TypeScript bridge-server moved to `_deprecated/`. OpenCode plugin restored as it's required for the plugin system to work.

### Priority 2: Verify Status ⚠️
1. Check Python code in `NEXUS/` - Are they legacy or FFI-only?
2. Check `src/voice-engine/` - FFI-only or business logic?
3. Check `src/compiler-pipeline/runtime/` - Needed for compilation?

### Priority 3: Continue Migration ⏳
1. Continue migrating `opencode-dev/` to PureScript/Haskell/Lean4
2. Remove TypeScript business logic as migration progresses

---

## 🔍 VERIFICATION CHECKLIST

Before deleting TypeScript directories:

- [ ] PureScript bridge-server compiles successfully
- [ ] PureScript bridge-server tests pass
- [ ] PureScript opencode-plugin compiles successfully  
- [ ] PureScript opencode-plugin tests pass
- [ ] No imports/references to TypeScript versions in codebase
- [ ] Documentation updated to remove TypeScript references
- [ ] CI/CD updated to use PureScript versions
- [ ] Build system (Nix) uses PureScript versions

---

## 📝 NOTES

**Language Stack Rule:**
> "No other languages permitted. No interop with untyped ecosystems."
> 
> **Implementation:** PureScript
> **Systems:** Haskell  
> **Verification:** Lean4

**Exceptions (if any):**
- FFI-only Python (like STRAYLIGHT Python wrappers) - Acceptable
- UI bindings TypeScript - May be acceptable for React/Vue integration
- Build scripts - May use typed languages (Haskell scripts preferred)

**Current Violations:**
- `src/bridge-server/` - Full TypeScript implementation (moved to `_deprecated/`, PureScript version active)
- `src/opencode-plugin/` - TypeScript plugin (required for OpenCode plugin system - exception)
- `opencode-dev/` - Large TypeScript codebase (migration in progress)
