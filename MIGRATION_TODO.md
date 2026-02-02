# Migration TODO - TypeScript to PureScript/Haskell/Lean4

**Last Updated:** 2026-02-02
**Session:** Migration session - preparing for box migration

---

## COMPLETED IN THIS SESSION

### 1. enterprise package - VERIFIED COMPLETE
- `share.ts` -> `packages/enterprise/src/core/src/Render/Core/Share.hs` (227 lines)
- `storage.ts` -> `packages/enterprise/src/core/src/Render/Core/Storage.hs` (186 lines)
- Both fully cover TypeScript functionality

### 2. util package - MIGRATED (10 files)
Location: `packages/util/src/`

| File | Status | Notes |
|------|--------|-------|
| Array.purs | DONE | findLast function |
| Binary.purs | DONE | search, insert for sorted arrays |
| Encode.purs + Encode.js | DONE | base64Encode/Decode, checksum (FFI) |
| Error.purs | DONE | NamedError type |
| Fn.purs | DONE | Validated function wrapper |
| Identifier.purs + Identifier.js | DONE | Monotonic ID generation (FFI) |
| Iife.purs | DONE | Immediately invoked function |
| Lazy.purs | DONE | Lazy evaluation with memoization |
| Path.purs | DONE | getFilename, getDirectory, etc. |
| Retry.purs + Retry.js | DONE | Retry with exponential backoff (FFI) |
| Slug.purs | DONE | Random slug generator |

### 3. app/voice - MIGRATED (4 files)
Location: `packages/app/src/Voice/`

| File | Status | Notes |
|------|--------|-------|
| AudioVisualizer.purs | DONE | Audio level visualizer component |
| MicrophoneButton.purs | DONE | Mic toggle with audio indicator |
| TranscriptView.purs | DONE | Voice transcript display |
| VoiceSelector.purs | DONE | Voice selection dropdown |

### 4. app/hooks - MIGRATED (2 files)
Location: `packages/app/src/Hooks/`

| File | Status | Notes |
|------|--------|-------|
| UseVoice.purs + UseVoice.js | DONE | Voice recording/transcription hook (FFI) |
| UseProviders.purs | DONE | Provider management hook |

### 5. app/i18n - BASE MIGRATED (3 files)
Location: `packages/app/src/I18n/`

| File | Status | Notes |
|------|--------|-------|
| Types.purs | DONE | Language enum, Dict type |
| En.purs | DONE | English base translations (subset) |
| I18n.purs | DONE | translate, getDictionary |

### 6. Skills - CREATED (3 files)
Location: `.opencode/skills/`

| Skill | Status | Notes |
|-------|--------|-------|
| deterministic-coder | DONE | MANDATORY for code modifications |
| exploratory-architect | DONE | MANDATORY for architecture design |
| expert-researcher | DONE | For research and analysis |

### 7. Structure Cleanup
- Removed nested `packages/util/src/src/` (was incorrect)
- Removed nested `packages/app/src/src/` (was incorrect)
- Fixed spago.yaml locations

---

## REMAINING MIGRATION WORK

### HIGH PRIORITY - app/context (21 files)
Source: `opencode-dev/packages/app/src/context/`
Target: `packages/app/src/Context/`

| File | Lines | Description | Priority |
|------|-------|-------------|----------|
| command.tsx | ~150 | Command context | HIGH |
| comments.tsx | ~100 | Comments context | MEDIUM |
| file.tsx | ~200 | File context | HIGH |
| global-sdk.tsx | ~150 | Global SDK context | HIGH |
| global-sync.tsx | ~300 | Global sync context | HIGH |
| highlights.tsx | ~100 | Highlights context | MEDIUM |
| language.tsx | ~80 | Language context | LOW |
| layout-scroll.ts | ~50 | Layout scroll utilities | LOW |
| layout.tsx | ~150 | Layout context | MEDIUM |
| local.tsx | ~100 | Local storage context | MEDIUM |
| models.tsx | ~200 | Models context | HIGH |
| notification.tsx | ~100 | Notification context | MEDIUM |
| permission.tsx | ~150 | Permission context | HIGH |
| platform.tsx | ~80 | Platform context | LOW |
| prompt.tsx | ~250 | Prompt context | HIGH |
| sdk.tsx | ~200 | SDK context | HIGH |
| server.tsx | ~150 | Server context | HIGH |
| settings.tsx | ~200 | Settings context | HIGH |
| sync.tsx | ~150 | Sync context | MEDIUM |
| terminal.tsx | ~200 | Terminal context | HIGH |
| layout-scroll.test.ts | ~50 | Tests | LOW |

### HIGH PRIORITY - app/pages (6 files)
Source: `opencode-dev/packages/app/src/pages/`
Target: `packages/app/src/Pages/`

| File | Lines | Description |
|------|-------|-------------|
| directory-layout.tsx | ~100 | Directory layout page |
| error.tsx | ~150 | Error page |
| home.tsx | ~200 | Home page |
| layout.tsx | ~100 | Main layout |
| session.tsx | ~300 | Session page |
| voice.tsx | ~150 | Voice page |

### MEDIUM PRIORITY - app/utils (14 files)
Source: `opencode-dev/packages/app/src/utils/`
Target: `packages/app/src/Utils/`

| File | Lines | Description |
|------|-------|-------------|
| agent.ts | ~50 | Agent utilities |
| base64.ts | ~30 | Base64 encoding |
| dom.ts | ~100 | DOM utilities |
| id.ts | ~30 | ID generation |
| index.ts | ~20 | Barrel export |
| maybe.ts | ~50 | Maybe/Option utilities |
| perf.ts | ~50 | Performance utilities |
| persist.ts | ~80 | Persistence utilities |
| prompt.ts | ~100 | Prompt utilities |
| same.ts | ~30 | Equality utilities |
| solid-dnd.tsx | ~150 | Solid.js DnD utilities |
| sound.ts | ~80 | Sound utilities |
| speech.ts | ~100 | Speech utilities |
| worktree.ts | ~100 | Git worktree utilities |

### MEDIUM PRIORITY - ui package (87 files)
Source: `opencode-dev/packages/ui/`
Target: `packages/ui/`

**Components (47 files):**
- Accordion, Alert, Avatar, Badge, Button, Card, Checkbox, Code
- Collapsible, Command, ContextMenu, Dialog, DropdownMenu
- Form, Icon, Input, Label, MenuBar, NavigationMenu, Popover
- Progress, RadioGroup, ScrollArea, Select, Separator, Sheet
- Skeleton, Slider, Sonner, Switch, Table, Tabs, Textarea
- Toast, Toggle, ToggleGroup, Tooltip, etc.

**i18n (15 files):** Same languages as app/i18n

**Context (9 files):**
- ErrorBoundary, GithubAuth, Language, Theme, Toast, etc.

**Theme (7 files):**
- Colors, Fonts, Spacing, etc.

**Hooks (3 files):**
- useDebounce, useMediaQuery, useWindowSize

### LOW PRIORITY - console package (156 files)
Source: `opencode-dev/packages/console/`
Target: `packages/console/`

**Routes (60+ files):**
- workspace (21), zen (18), auth (5), black (4), download (3)
- bench (3), docs (2), legal (2), etc.

**Components (~40 files):**
- Various UI components for web console

**Context (~20 files):**
- React contexts for console

**Lib (~15 files):**
- Utility functions

### LOW PRIORITY - SDK strategy
Decision needed: Generate JS SDK from PureScript types?
- Current: 40 TypeScript files in `opencode-dev/packages/sdk/`
- Options:
  1. Keep as TypeScript (for npm distribution)
  2. Generate from PureScript types
  3. Migrate to PureScript and compile to JS

### EXCLUDED FROM MIGRATION (Platform-specific)
These should remain TypeScript:
- `desktop/` (26 files) - Electron/Tauri
- `web/` (16 files) - SST/AWS deployment
- `slack/` (2 files) - Slack integration
- `containers/` (1 file) - Docker configs

---

## FILE COUNTS SUMMARY

| Package | TS Files | PS Files | Status | Gap |
|---------|----------|----------|--------|-----|
| opencode | 313 | 450+ | DONE | +137 |
| enterprise | 18 | 18 | DONE | 0 |
| util | 12 | 14 | DONE | +2 |
| app | 163 | ~30 | IN PROGRESS | -133 |
| plugin | 6 | 8 | DONE | +2 |
| ui | 87 | 0 | TODO | -87 |
| console | 156 | 0 | TODO | -156 |
| sdk | 40 | 0 | DECIDE | -40 |

---

## TECHNICAL NOTES

### PureScript Module Structure
```
packages/<name>/
  spago.yaml           # Package config
  src/
    ModuleName.purs    # PureScript source
    ModuleName.js      # FFI (if needed)
```

### Key Dependencies (in flake.nix)
- PureScript: purescript-overlay
- Haskell: haskellPackages
- Lean4: lean4

### Build Commands
```bash
# Build all
nix build .#all-packages

# Build specific
nix build .#opencode-types-ps
nix build .#sidepanel-ps

# Dev shell
nix develop
```

### FFI Pattern
When migrating TS that uses browser APIs:
1. Create `.purs` file with `foreign import` declarations
2. Create `.js` file with ES module exports
3. Match function signatures exactly

### Protocol Requirements (from deterministic-coder skill)
1. Read complete files before modification
2. Trace dependency graph (upstream/downstream)
3. No banned constructs (any, unknown, as, etc.)
4. Explicit types at function boundaries
5. Update documentation after changes

---

## NEXT SESSION CHECKLIST

1. [ ] Pull latest from origin
2. [ ] Load `deterministic-coder` skill
3. [ ] Continue with app/context migration (21 files)
4. [ ] Read each TypeScript file completely before migrating
5. [ ] Create PureScript equivalent in `packages/app/src/Context/`
6. [ ] Add FFI files where browser APIs are used
7. [ ] Update MIGRATION_PARITY_REPORT.md after each category
8. [ ] Commit and push regularly

---

## KNOWN ISSUES

1. **Nested src directories** - Previously had `src/src/` nesting, now cleaned up
2. **spago.dhall vs spago.yaml** - Some packages use old dhall format, migrate to yaml
3. **Missing packages.dhall** - Needed for spago dependencies
4. **Build caches cleared** - Will need to reinstall dependencies

---

## CONTACTS / REFERENCES

- OpenCode docs: https://opencode.ai/docs
- PureScript docs: https://pursuit.purescript.org
- Haskell docs: https://hoogle.haskell.org
- Lean4 docs: https://leanprover.github.io

---

*This TODO was created during migration session on 2026-02-02*
