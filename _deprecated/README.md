# Deprecated Code Directory

**Status:** This directory contains legacy code that has been deprecated and moved out of the main codebase.

**Git Status:** This entire directory is excluded from git (see root `.gitignore`).

---

## Contents

### Code

#### `src/bridge-server/` - TypeScript Bridge Server (Legacy)
**Moved from:** `src/bridge-server/`  
**Status:** Deprecated - PureScript version exists at `src/bridge-server-ps/`  
**Reason:** Violates language stack (PureScript/Haskell/Lean4 only)

**Replacement:** Use `src/bridge-server-ps/` instead.

---

#### `src/opencode-plugin/` - TypeScript OpenCode Plugin ✅ RESTORED
**Status:** Active - Required for OpenCode plugin system  
**Reason:** OpenCode loads plugins from npm/local files - this is the plugin that gets loaded  
**Note:** PureScript version (`src/opencode-plugin-ps/`) compiles to JavaScript, but this TypeScript version is needed for the plugin system to work

---

### Documentation

#### `docs/VERIFICATION_AND_TESTING_PLAN.md` - Implementation Plan
**Moved from:** `docs/VERIFICATION_AND_TESTING_PLAN.md`  
**Status:** Deprecated - Contains implementation plans, phases, and TODO items  
**Reason:** Not current project documentation, contains future plans

---

#### `docs/MIGRATION.md` - Migration Plan
**Moved from:** `docs/MIGRATION.md`  
**Status:** Deprecated - Contains migration strategies and plans  
**Reason:** Not current project documentation, contains implementation plans

---

#### `docs/BRIDGE_SERVER_IMPLEMENTATION.md` - Implementation Plan
**Moved from:** `docs/BRIDGE_SERVER_IMPLEMENTATION.md`  
**Status:** Deprecated - Contains implementation plans, phases, and TODO items  
**Reason:** Not current project documentation, contains future plans

---

#### `docs/DEEP_TESTING_STANDARDS.md` - Implementation Plan
**Moved from:** `docs/DEEP_TESTING_STANDARDS.md`  
**Status:** Deprecated - Contains implementation plans, phases, and TODO items  
**Reason:** Not current project documentation, contains future plans

---

#### `docs/decisions/0002-migration-strategy.md` - Migration ADR
**Moved from:** `docs/decisions/0002-migration-strategy.md`  
**Status:** Deprecated - Contains migration plans (Status: "Proposed")  
**Reason:** Not current project documentation, contains future plans

---

## Why Keep This Directory?

This directory is kept locally for:
- Reference during migration
- Historical context
- Debugging legacy issues if needed

**Important:** This directory is **NOT pushed to git**. It exists only in local workspaces.

---

## Active Code Locations

- **Bridge Server:** `src/bridge-server-ps/` (PureScript)
- **OpenCode Plugin:** `src/opencode-plugin-ps/` (PureScript)
- **OpenCode Fork:** `opencode-dev/` (TypeScript/Bun - active fork for extensions)

---

## Notes

- The `opencode-dev/` directory remains in the main codebase as it's the active fork for extensions/plugins
- All PureScript/Haskell/Lean4 implementations are in `src/` and remain active
- This deprecated code may be deleted entirely once migration is complete
