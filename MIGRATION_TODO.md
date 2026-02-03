# Migration TODO - TypeScript to PureScript/Haskell/Lean4

**Last Updated:** 2026-02-03
**Session:** Consolidation and continued migration

---

## CANONICAL SOURCE

**TypeScript Reference:** `_OTHER/opencode-original/packages/`

> **IMPORTANT:** Always use `_OTHER/opencode-original/` as the source of truth.
> The `opencode-dev/` directory has been archived to `_archived/opencode-dev-merged-2026-02-03/`
> after merging its additions (voice features, tests) into opencode-original.

See `MIGRATION_CHECKLIST.md` for the complete workflow.

---

## COMPLETED IN PREVIOUS SESSIONS

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

### 6. app/context - MIGRATED (20 files)
Location: `packages/app/src/Context/`

| File | Status | Notes |
|------|--------|-------|
| Command.purs | DONE | Keybindings and command palette |
| Comments.purs | DONE | Line comments on files |
| File.purs | DONE | File loading and tree navigation |
| GlobalSDK.purs | DONE | Global OpenCode client |
| GlobalSync.purs | DONE | Global state synchronization |
| Highlights.purs | DONE | Release notes highlights |
| Language.purs | DONE | i18n localization |
| Layout.purs | DONE | UI layout state |
| LayoutScroll.purs | DONE | Scroll persistence |
| Local.purs | DONE | Local session state (agent/model) |
| Models.purs | DONE | AI model selection/visibility |
| Notification.purs | DONE | App notifications |
| Permission.purs | DONE | Auto-accept permissions |
| Platform.purs | DONE | Platform capabilities |
| Prompt.purs | DONE | Prompt input state |
| SDK.purs | DONE | OpenCode SDK client |
| Server.purs | DONE | Server connections |
| Settings.purs | DONE | User preferences |
| Sync.purs | DONE | Session data synchronization |
| Terminal.purs | DONE | Terminal/PTY sessions |

### 7. Skills - CREATED (3 files)
Location: `.opencode/skills/`

| Skill | Status | Notes |
|-------|--------|-------|
| deterministic-coder | DONE | MANDATORY for code modifications |
| exploratory-architect | DONE | MANDATORY for architecture design |
| expert-researcher | DONE | For research and analysis |

### 8. Structure Cleanup
- Removed nested `packages/util/src/src/` (was incorrect)
- Removed nested `packages/app/src/src/` (was incorrect)
- Fixed spago.yaml locations

---

## REMAINING MIGRATION WORK

### ~~HIGH PRIORITY - app/context (21 files)~~ COMPLETED
See Section 6 above - all 20 context files migrated.
(layout-scroll.test.ts is a test file, not a context)

### ~~HIGH PRIORITY - app/pages (6 files)~~ COMPLETED
Source: `_OTHER/opencode-original/packages/app/src/pages/`
Target: `packages/app/src/Pages/`

| File | Target | Lines | Status |
|------|--------|-------|--------|
| directory-layout.tsx | DirectoryLayout.purs | 72 | DONE |
| error.tsx | Error.purs | 291 | DONE |
| home.tsx | Home.purs | 127 | DONE |
| layout.tsx | Layout.purs | 2902 | DONE |
| session.tsx | Session.purs | 1651 | DONE |
| voice.tsx | Voice.purs | 298 | DONE |

### ~~MEDIUM PRIORITY - app/utils (14 files)~~ COMPLETED
Source: `_OTHER/opencode-original/packages/app/src/utils/`
Target: `packages/app/src/Utils/`

| File | Target | Lines | Status |
|------|--------|-------|--------|
| agent.ts | Agent.purs | 12 | DONE |
| base64.ts | Base64.purs | 11 | DONE |
| dom.ts | Dom.purs | 52 | DONE |
| id.ts | Id.purs | 100 | DONE |
| index.ts | (re-exports) | 2 | DONE |
| maybe.ts | Maybe.purs | 67 | DONE |
| perf.ts | Perf.purs | 136 | DONE |
| persist.ts | Persist.purs | 452 | DONE |
| prompt.ts | Prompt.purs | 204 | DONE |
| same.ts | Same.purs | 7 | DONE |
| solid-dnd.tsx | SolidDnd.purs | 56 | DONE |
| sound.ts | Sound.purs | 118 | DONE |
| speech.ts | Speech.purs | 329 | DONE |
| worktree.ts | Worktree.purs | 74 | DONE |

### ~~MEDIUM PRIORITY - app/addons (2 files)~~ COMPLETED
Source: `_OTHER/opencode-original/packages/app/src/addons/`
Target: `packages/app/src/addons/`

| File | Target | Lines | Status |
|------|--------|-------|--------|
| serialize.ts | Serialize.purs | 200 | DONE |
| serialize.test.ts | Serialize.Spec.purs | 242 | DONE |

### HIGH PRIORITY - ui package (87 files)
Source: `_OTHER/opencode-original/packages/ui/`
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
Source: `_OTHER/opencode-original/packages/console/`
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
- Current: 40 TypeScript files in `_OTHER/opencode-original/packages/sdk/`
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
| app | 163 | ~121 | DONE | -42 (tests only) |
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
3. [x] Complete app/context migration (20 files) - DONE 2026-02-02
4. [x] Complete app/pages migration (6 files) - DONE 2026-02-02
5. [x] Complete app/utils migration (14 files) - DONE 2026-02-02
6. [x] Complete app/addons migration (2 files) - DONE 2026-02-02
7. [ ] Begin ui package migration (87 files)
8. [ ] Read each TypeScript file completely before migrating
9. [ ] Add FFI files where browser APIs are used
10. [ ] Update MIGRATION_PARITY_REPORT.md after each category
11. [ ] Commit and push regularly

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
