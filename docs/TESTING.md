# Forge Comprehensive Test Plan

> **Generated**: 2026-02-07
> **Status**: Living document -- updated with each test cycle
> **Owner**: Engineering

---

## 1. Overview and Metrics

### 1.1 Current State

| Metric | Value |
|---|---|
| Total tests | 2,919 |
| Property tests | 97 |
| Estimated coverage | ~25-30% |
| Test files | 113 (56 TypeScript, 30 PureScript, 15 Haskell, 12 integration) |
| Packages tested | 6 of 11 |

### 1.2 Target State

| Metric | Target |
|---|---|
| Total tests | 8,000+ |
| Property tests | 500+ |
| Coverage (forge-core) | 80%+ |
| Coverage (app) | 70%+ |
| Coverage (ui) | 60%+ |
| Coverage (forge/server) | 80%+ |
| Coverage (enterprise) | 90%+ |
| Coverage (console) | 75%+ |
| Coverage (opencode) | 80%+ |

### 1.3 Package Summary

| Package | Source Modules | Existing Test Files | Gap |
|---|---|---|---|
| forge-core | 204 PureScript | 3 Haskell specs | ~200 untested |
| app | 70 PureScript | 11 PureScript specs | ~59 untested |
| ui | 88 PureScript | 0 | 88 untested |
| forge/server | 46 PS + 15 HS | 24 PS + 7 HS specs | ~30 untested |
| forge/types | 11 PureScript | 0 | 11 untested |
| forge/util | 4 Haskell | 3 Haskell specs | ~1 untested |
| enterprise | 18 HS/PS | 0 | 18 untested |
| console | 131 PureScript | 32 PureScript specs | ~99 untested |
| opencode | 157 TypeScript | 56 TS test files | ~101 untested |

---

## 2. Test Infrastructure

### 2.1 PureScript (purescript-spec + purescript-quickcheck via spago test)

```bash
cd packages/forge-core && spago test
cd packages/app && spago test
cd packages/ui && spago test
cd packages/forge/src/server && spago test
cd packages/forge/src/plugin && spago test
cd packages/console/app && spago test
cd packages/console/core && spago test
```

- **Framework**: purescript-spec for unit/integration, purescript-quickcheck for property tests
- **Assertion style**: shouldEqual, shouldSatisfy, shouldContain
- **Property style**: quickCheck, quickCheckGen with custom Arbitrary instances
- **Mocking**: Manual mocks via record-of-functions pattern

### 2.2 Haskell (HSpec + QuickCheck via cabal test)

```bash
cd packages/forge-core && cabal test
cd packages/forge/src/storage && cabal test
cd packages/forge/src/storage/analytics && cabal test
cd packages/enterprise/src/gateway && cabal test
```

- **Framework**: hspec for unit/integration, QuickCheck for property tests
- **Assertion style**: shouldBe, shouldSatisfy, shouldThrow
- **Property style**: property, forAll with custom Arbitrary instances
- **Database tests**: Use tmp-postgres or in-memory SQLite for isolation

### 2.3 Lean4 (theorem proving via lake build)

```bash
cd packages/forge-core/src/permission/lean && lake build
```

- **Approach**: Compile-time verification via dependent types
- **Properties proven**: Permission lattice correctness, arity bounds, monotonicity
- **No runtime tests needed**: If it compiles, it is correct

### 2.4 TypeScript (Bun test)

```bash
cd packages/opencode && bun test
bun test --filter "session"
bun test test/tool/bash.test.ts
```

- **Framework**: Bun built-in test runner
- **Assertion style**: expect().toBe(), expect().toEqual(), expect().toThrow()
- **Mocking**: mock() from bun:test
- **Coverage**: bun test --coverage

### 2.5 CI Pipeline

```yaml
# Required checks before merge
- spago-test-forge-core
- spago-test-app
- spago-test-ui
- spago-test-forge-server
- spago-test-console
- cabal-test-storage
- cabal-test-analytics
- cabal-test-enterprise
- bun-test-opencode
- lean-build-proofs
- coverage-threshold-check
```

### 2.6 Coverage Enforcement

| Package | Minimum | Enforced By |
|---|---|---|
| forge-core | 80% | CI gate |
| app | 70% | CI gate |
| ui | 60% | CI warning |
| forge/server | 80% | CI gate |
| enterprise | 90% | CI gate |
| console | 75% | CI gate |
| opencode | 80% | CI gate |

---

## 3. Property-Based Testing Strategy

### 3.1 Arbitrary Instance Guidelines

All domain types MUST have Arbitrary instances. Use frequency for realistic distributions:

- Messages: 80% text, 15% tool calls, 3% errors, 2% system
- Session sizes: geometric distribution mean=20, max=500
- Token counts: log-normal distribution matching LLM output patterns
- Error rates: 50% network, 20% auth, 10% provider, 1% data corruption, 19% timeout

### 3.2 Required Properties Per Module Type

| Module Type | Required Properties |
|---|---|
| Codec modules | Roundtrip decode.encode=id; Partial decode safety; Schema backward compat |
| State modules | Invariant preservation; Reducer commutativity where applicable |
| Tool modules | Idempotency where applicable; Output bounded; Error domain coverage |
| FFI modules | Null safety; Type coercion correctness; Exception containment |
| Auth modules | Token expiry monotonic; Permission lattice; No privilege escalation |
| Provider modules | Request format compliance; Response parsing completeness; Backoff monotonic |

### 3.3 Shrinking Strategy

- Shrink session = remove last message (preserves conversation structure)
- Shrink message = reduce content length, never remove required fields
- Custom shrinkers MUST preserve type invariants during shrinking

### 3.4 Test Timeout Policy

| Test Type | Timeout |
|---|---|
| Unit test | 5 seconds |
| Property test (100 iterations) | 30 seconds |
| Integration test | 60 seconds |
| E2E test | 120 seconds |
| Database test | 30 seconds |

---

## 4. forge-core (204 modules)

### 4.1 ACP
#### Forge.ACP.Agent
test line
testing append
test1
test2
test3

## 4. forge-core (204 modules)

### 4.1 ACP

#### Forge.ACP.Agent
- **File**: packages/forge-core/src/acp/Agent.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Agent registration; duplicate ID rejected | **Property**: prop_agentIdUnique

#### Forge.ACP.Session
- **File**: packages/forge-core/src/acp/Session.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Session created; messages routed | **Property**: prop_sessionMessageOrdering

#### Forge.ACP.Types
- **File**: packages/forge-core/src/acp/Types.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Type constructors valid; JSON codec roundtrips | **Property**: prop_codecRoundtrip

### 4.2 Agent

#### Forge.Agent.Agent
- **File**: packages/forge-core/src/agent/Agent.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Init state; process queue; concurrent tool calls; max iterations | **Property**: prop_agentAlwaysTerminates


### 4.3 Auth

#### Forge.Auth.Index
- **File**: packages/forge-core/src/auth/Index.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Token validated; expired rejected; refresh rotated | **Property**: prop_tokenExpiryMonotonic

### 4.4 Bridge

#### Forge.Bridge.FFI.Node.Process
- **File**: packages/forge-core/src/bridge/FFI/Node/Process.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Env vars read; exit code captured; signal handling | **Property**: prop_envVarReadWriteRoundtrip

#### Forge.Bridge.Utils.Validation
- **File**: packages/forge-core/src/bridge/Utils/Validation.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Valid input passes; invalid rejected; boundary values | **Property**: prop_validationIdempotent

### 4.5 Bun

#### Forge.Bun.Index
- **File**: packages/forge-core/src/bun/Index.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Runtime detected; APIs wrapped; fallback for non-Bun | **Property**: N/A


### 4.6 Bus

#### Forge.Bus.BusEvent
- **File**: packages/forge-core/src/bus/BusEvent.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Event constructors correct tags; payload serializes | **Property**: prop_eventCodecRoundtrip

#### Forge.Bus.Global
- **File**: packages/forge-core/src/bus/Global.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Singleton created; subscribers receive events; unsubscribe works | **Property**: prop_allSubscribersReceiveEvent

#### Forge.Bus.Index
- **File**: packages/forge-core/src/bus/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Re-exports all bus types | **Property**: N/A

### 4.7 CLI

#### Forge.CLI.Bootstrap
- **File**: packages/forge-core/src/cli/Bootstrap.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Init all subsystems; missing config defaults; env override | **Property**: prop_bootstrapIdempotent

#### Forge.CLI.Error
- **File**: packages/forge-core/src/cli/Error.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Error messages formatted; exit codes mapped; context preserved | **Property**: prop_errorCodeBounded

#### Forge.CLI.Logo
- **File**: packages/forge-core/src/cli/Logo.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Logo renders non-empty; fits terminal width | **Property**: N/A

#### Forge.CLI.Network
- **File**: packages/forge-core/src/cli/Network.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Connectivity check; proxy settings; timeout; DNS failure | **Property**: prop_networkCheckTerminates

#### Forge.CLI.UI
- **File**: packages/forge-core/src/cli/UI.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Spinner renders; progress bar; prompt reads; colors | **Property**: N/A

#### Forge.CLI.Upgrade
- **File**: packages/forge-core/src/cli/Upgrade.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Version check valid semver; upgrade flag; binary replacement | **Property**: prop_versionCompareTransitive


### 4.8 CLI Commands

#### Forge.CLI.Cmd.Acp
- **File**: packages/forge-core/src/cli/cmd/Acp.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Parses valid args; invalid shows help; session starts | **Property**: prop_argParseRoundtrip

#### Forge.CLI.Cmd.Agent
- **File**: packages/forge-core/src/cli/cmd/Agent.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Starts agent; lists active; stops gracefully | **Property**: prop_agentStartStopIdempotent

#### Forge.CLI.Cmd.Auth
- **File**: packages/forge-core/src/cli/cmd/Auth.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Login flow; logout clears creds; status shows provider | **Property**: prop_authStateConsistent

#### Forge.CLI.Cmd.Cmd
- **File**: packages/forge-core/src/cli/cmd/Cmd.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Router dispatches; unknown shows help; help flag works | **Property**: prop_commandDispatchDeterministic

#### Forge.CLI.Cmd.Export
- **File**: packages/forge-core/src/cli/cmd/Export.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Export to JSON; export to markdown; handles empty | **Property**: prop_exportImportRoundtrip

#### Forge.CLI.Cmd.Generate
- **File**: packages/forge-core/src/cli/cmd/Generate.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Creates valid output; template vars substituted | **Property**: N/A

#### Forge.CLI.Cmd.Github
- **File**: packages/forge-core/src/cli/cmd/Github.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Issue created; PR created; auth token used; rate limit | **Property**: N/A

#### Forge.CLI.Cmd.Import
- **File**: packages/forge-core/src/cli/cmd/Import.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Import JSON session; reject corrupt; merge existing | **Property**: prop_importPreservesMessageCount

#### Forge.CLI.Cmd.Mcp
- **File**: packages/forge-core/src/cli/cmd/Mcp.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: MCP server starts; tool list; tool invocation; auth handshake | **Property**: prop_mcpToolListStable

#### Forge.CLI.Cmd.Models
- **File**: packages/forge-core/src/cli/cmd/Models.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Lists all providers; model info; selection persists | **Property**: prop_modelListNonEmpty

#### Forge.CLI.Cmd.Pr
- **File**: packages/forge-core/src/cli/cmd/Pr.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: PR review starts; diff loaded; comments parsed | **Property**: N/A

#### Forge.CLI.Cmd.Run
- **File**: packages/forge-core/src/cli/cmd/Run.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Non-interactive run; tool calls; max iterations; stdout | **Property**: prop_runAlwaysTerminates

#### Forge.CLI.Cmd.Serve
- **File**: packages/forge-core/src/cli/cmd/Serve.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Starts on port; concurrent connections; graceful shutdown | **Property**: prop_serverPortBounded

#### Forge.CLI.Cmd.Session
- **File**: packages/forge-core/src/cli/cmd/Session.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: List all; resume; delete confirmed; share URL | **Property**: prop_sessionListContainsAll

#### Forge.CLI.Cmd.Stats
- **File**: packages/forge-core/src/cli/cmd/Stats.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Token usage; cost; empty history; time range | **Property**: prop_statsTotalEqualsSum

#### Forge.CLI.Cmd.Uninstall
- **File**: packages/forge-core/src/cli/cmd/Uninstall.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Confirms; removes files; cleans config | **Property**: N/A

#### Forge.CLI.Cmd.Upgrade
- **File**: packages/forge-core/src/cli/cmd/Upgrade.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Checks version; downloads binary; atomic replace; rollback | **Property**: prop_upgradeVersionMonotonic

#### Forge.CLI.Cmd.Web
- **File**: packages/forge-core/src/cli/cmd/Web.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Opens browser; starts local server; URL fallback | **Property**: N/A


### 4.9 CLI Debug

#### Forge.CLI.Cmd.Debug.Agent
- **File**: packages/forge-core/src/cli/cmd/debug/Agent.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Shows internal state; dumps config; traces message flow | **Property**: N/A

#### Forge.CLI.Cmd.Debug.Config
- **File**: packages/forge-core/src/cli/cmd/debug/Config.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Shows resolved config; shows sources; validates | **Property**: N/A

#### Forge.CLI.Cmd.Debug.File
- **File**: packages/forge-core/src/cli/cmd/debug/File.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Shows metadata; encoding; permissions | **Property**: N/A

#### Forge.CLI.Cmd.Debug.Index
- **File**: packages/forge-core/src/cli/cmd/debug/Index.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Routes to subcommands; help shows all | **Property**: N/A

#### Forge.CLI.Cmd.Debug.Lsp
- **File**: packages/forge-core/src/cli/cmd/debug/Lsp.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Shows running servers; capabilities; traces | **Property**: N/A

#### Forge.CLI.Cmd.Debug.Ripgrep
- **File**: packages/forge-core/src/cli/cmd/debug/Ripgrep.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Shows binary path; test search; version | **Property**: N/A

#### Forge.CLI.Cmd.Debug.Scrap
- **File**: packages/forge-core/src/cli/cmd/debug/Scrap.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Executes playground code; output captured | **Property**: N/A

#### Forge.CLI.Cmd.Debug.Skill
- **File**: packages/forge-core/src/cli/cmd/debug/Skill.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Lists skills; shows content; validates syntax | **Property**: N/A

#### Forge.CLI.Cmd.Debug.Snapshot
- **File**: packages/forge-core/src/cli/cmd/debug/Snapshot.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Lists snapshots; shows diff; restore preview | **Property**: N/A

### 4.10 CLI TUI

#### Forge.CLI.Cmd.TUI.Attach
- **File**: packages/forge-core/src/cli/cmd/tui/Attach.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Connects to server; displays session; reconnects | **Property**: N/A

#### Forge.CLI.Cmd.TUI.Event
- **File**: packages/forge-core/src/cli/cmd/tui/Event.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Events dispatched correctly; key mapping; resize propagated | **Property**: prop_eventHandlerTotal

#### Forge.CLI.Cmd.TUI.Thread
- **File**: packages/forge-core/src/cli/cmd/tui/Thread.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Renders message list; streaming updates; auto-scroll; history | **Property**: prop_threadMessageOrderPreserved

#### Forge.CLI.Cmd.TUI.Worker
- **File**: packages/forge-core/src/cli/cmd/tui/Worker.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Background tasks; cancellation; progress; concurrency limit | **Property**: prop_workerConcurrencyBounded

#### Forge.CLI.Cmd.TUI.Component.TextareaKeybindings
- **File**: packages/forge-core/src/cli/cmd/tui/component/TextareaKeybindings.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Enter submits; Shift+Enter newline; Ctrl+C cancels | **Property**: prop_keybindingsNoConflict

#### Forge.CLI.Cmd.TUI.Context.Directory
- **File**: packages/forge-core/src/cli/cmd/tui/context/Directory.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Shows cwd; change updates prompt | **Property**: N/A

#### Forge.CLI.Cmd.TUI.UI.Spinner
- **File**: packages/forge-core/src/cli/cmd/tui/ui/Spinner.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Animates; stops on complete; shows label | **Property**: N/A

#### Forge.CLI.Cmd.TUI.Util.Clipboard
- **File**: packages/forge-core/src/cli/cmd/tui/util/Clipboard.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Copy; paste; empty handled | **Property**: prop_clipboardRoundtrip

#### Forge.CLI.Cmd.TUI.Util.Editor
- **File**: packages/forge-core/src/cli/cmd/tui/util/Editor.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Opens file; waits for close; detects EDITOR; fallback | **Property**: N/A

#### Forge.CLI.Cmd.TUI.Util.Signal
- **File**: packages/forge-core/src/cli/cmd/tui/util/Signal.purs | **Tests**: None | **Priority**: LOW
- **Unit**: SIGINT handled; SIGTERM handled; cleanup | **Property**: N/A

#### Forge.CLI.Cmd.TUI.Util.Terminal
- **File**: packages/forge-core/src/cli/cmd/tui/util/Terminal.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Size detected; raw mode; alternate screen; cursor | **Property**: prop_terminalSizePositive

#### Forge.CLI.Cmd.TUI.Util.Transcript
- **File**: packages/forge-core/src/cli/cmd/tui/util/Transcript.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Records messages; exports markdown; filters by role | **Property**: prop_transcriptLengthMonotonic


### 4.11 Command, Config, Env, File

#### Forge.Command.Index
- **File**: packages/forge-core/src/command/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Registry contains all; lookup by name; alias resolution | **Property**: prop_commandNameUnique

#### Forge.Config.Config
- **File**: packages/forge-core/src/config/Config.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Loads from file; merges layers; validates required; watches changes | **Property**: prop_configMergeAssociative

#### Forge.Config.Markdown
- **File**: packages/forge-core/src/config/Markdown.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Config parsed; frontmatter extracted; code blocks identified | **Property**: prop_markdownParseRoundtrip

#### Forge.Env.Index
- **File**: packages/forge-core/src/env/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Env vars read; missing returns Nothing; type coercion; XDG paths | **Property**: prop_envReadConsistent

#### Forge.File.File
- **File**: packages/forge-core/src/file/File.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Read contents; write creates; permissions; binary detection; encoding | **Property**: prop_fileReadWriteRoundtrip

#### Forge.File.Ignore
- **File**: packages/forge-core/src/file/Ignore.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: gitignore patterns; nested ignore; negation; directory patterns | **Property**: prop_ignorePatternIdempotent

#### Forge.File.Index
- **File**: packages/forge-core/src/file/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Re-exports; file listing; tree construction | **Property**: N/A

#### Forge.File.Ripgrep
- **File**: packages/forge-core/src/file/Ripgrep.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Search matches; regex; file type filter; max results; binary skip | **Property**: prop_searchResultsContainPattern

#### Forge.File.Time
- **File**: packages/forge-core/src/file/Time.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Mtime read; ctime read; comparison; formatting | **Property**: prop_timeMonotonic

#### Forge.File.Watcher
- **File**: packages/forge-core/src/file/Watcher.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Detects changes; new files; deletions; debounce; respects ignore | **Property**: prop_watcherEventuallyFires

### 4.12 Flag, Format, Global, Id, IDE, Installation

#### Forge.Flag.Flag
- **File**: packages/forge-core/src/flag/Flag.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Flag checked; default value; env override; config override | **Property**: prop_flagDeterministic

#### Forge.Format.Formatter
- **File**: packages/forge-core/src/format/Formatter.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Format message; code blocks; tool results; errors | **Property**: prop_formatOutputNonEmpty

#### Forge.Format.Index
- **File**: packages/forge-core/src/format/Index.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Re-exports correctly | **Property**: N/A

#### Forge.Global.Index
- **File**: packages/forge-core/src/global/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: State initialized; accessible from any module; cleanup | **Property**: prop_globalStateConsistent

#### Forge.Id.Id
- **File**: packages/forge-core/src/id/Id.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Non-empty; unique across calls; correct prefix; serializes | **Property**: prop_idUnique, prop_idCodecRoundtrip

#### Forge.IDE.Index
- **File**: packages/forge-core/src/ide/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: IDE detection; IDE-specific config; integration features | **Property**: prop_ideDetectionConsistent

#### Forge.Installation.Index
- **File**: packages/forge-core/src/installation/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Path resolved; version detected; integrity checked | **Property**: N/A


### 4.13 LSP

#### Forge.LSP.Client
- **File**: packages/forge-core/src/lsp/Client.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Starts server; sends initialize; definition; completion; reconnect | **Property**: prop_lspRequestResponsePaired

#### Forge.LSP.Index
- **File**: packages/forge-core/src/lsp/Index.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Re-exports correctly | **Property**: N/A

#### Forge.LSP.Language
- **File**: packages/forge-core/src/lsp/Language.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Language from extension; shebang; server binary; settings | **Property**: prop_languageDetectionDeterministic

#### Forge.LSP.Server
- **File**: packages/forge-core/src/lsp/Server.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Process spawned; stdio; malformed JSON; init handshake; clean shutdown | **Property**: prop_serverProcessIsolation

### 4.14 MCP

#### Forge.MCP.Auth
- **File**: packages/forge-core/src/mcp/Auth.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: OAuth flow; callback code exchange; token stored; refresh | **Property**: prop_tokenRefreshBeforeExpiry

#### Forge.MCP.Index
- **File**: packages/forge-core/src/mcp/Index.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Server list; tool list aggregated; tool invocation; health check | **Property**: prop_mcpToolNamesUnique

#### Forge.MCP.OAuthCallback
- **File**: packages/forge-core/src/mcp/OAuthCallback.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Callback server starts; receives code; exchanges token; CSRF validated | **Property**: prop_callbackStateMatchesRequest

#### Forge.MCP.OAuthProvider
- **File**: packages/forge-core/src/mcp/OAuthProvider.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Config loaded; auth URL constructed; token endpoint; scope | **Property**: prop_authUrlContainsRequiredParams

### 4.15 Patch, Permission

#### Forge.Patch.Index
- **File**: packages/forge-core/src/patch/Index.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Applies cleanly; rejects conflict; multiple hunks; permissions; empty no-op | **Property**: prop_patchApplyRevert

#### Forge.Permission.Arity
- **File**: packages/forge-core/src/permission/Arity.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Bounds checked; exceeded triggers error; zero means disabled | **Property**: prop_arityBoundedNonNegative

#### Forge.Permission.Index
- **File**: packages/forge-core/src/permission/Index.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Allows authorized; denies unauthorized; escalation blocked; cached | **Property**: prop_permissionLatticePreserved

#### Forge.Permission.Next
- **File**: packages/forge-core/src/permission/Next.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Next state computed; auto-approve threshold; deny persists | **Property**: prop_nextPermissionDeterministic

### 4.16 Plugin

#### Forge.Plugin.Codex
- **File**: packages/forge-core/src/plugin/Codex.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Plugin loads; tool registered; output parsed; error handled | **Property**: N/A

#### Forge.Plugin.Copilot
- **File**: packages/forge-core/src/plugin/Copilot.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Plugin loads; auth integrated; completions forwarded | **Property**: N/A

#### Forge.Plugin.Index
- **File**: packages/forge-core/src/plugin/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Registry lists all; load/unload lifecycle; isolation; config merged | **Property**: prop_pluginNamesUnique


### 4.17 Project

#### Forge.Project.Bootstrap
- **File**: packages/forge-core/src/project/Bootstrap.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Detected from cwd; root found via markers; nested handled; no-project mode | **Property**: prop_projectRootIsAncestorOfCwd

#### Forge.Project.Instance
- **File**: packages/forge-core/src/project/Instance.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Instance created; unique ID; tracks sessions; cleanup | **Property**: prop_instanceIdUnique

#### Forge.Project.Project
- **File**: packages/forge-core/src/project/Project.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Metadata loaded; type detected; files enumerated; config merged | **Property**: prop_projectTypeDetectionConsistent

#### Forge.Project.State
- **File**: packages/forge-core/src/project/State.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: State persisted; restored on restart; migrations; corrupt recovery | **Property**: prop_stateCodecRoundtrip

#### Forge.Project.VCS
- **File**: packages/forge-core/src/project/VCS.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Git detected; current branch; uncommitted changes; commit history | **Property**: N/A

### 4.18 Provider

#### Forge.Provider.Auth
- **File**: packages/forge-core/src/provider/Auth.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: API key validated; from env; from config; provider-specific headers | **Property**: prop_authHeaderNonEmpty

#### Forge.Provider.Models
- **File**: packages/forge-core/src/provider/Models.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Model list populated; context window; pricing; capability flags | **Property**: prop_modelContextWindowPositive

#### Forge.Provider.Provider
- **File**: packages/forge-core/src/provider/Provider.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Registered; selected; fallback chain; rate limit; all enumerable | **Property**: prop_providerFallbackTerminates

#### Forge.Provider.Transform
- **File**: packages/forge-core/src/provider/Transform.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Message format transformed; tool calls; response normalized; streaming assembled | **Property**: prop_transformRoundtrip

### 4.19 Provider SDK (OpenAI Compatible) -- 14 modules

#### Forge.Provider.SDK.OpenAICompatible.Index
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/Index.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Exports all types; creates client; handles auth | **Property**: N/A

#### Forge.Provider.SDK.OpenAICompatible.Provider
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/Provider.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Makes API call; streaming; non-streaming; retries 429; handles 500 | **Property**: prop_providerRetriesMonotonic

#### Forge.Provider.SDK.Responses.ConvertToOpenAIResponsesInput
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/ConvertToOpenAIResponsesInput.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Text converted; tool call; system message; multi-part | **Property**: prop_conversionPreservesContent

#### Forge.Provider.SDK.Responses.MapFinishReason
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/MapOpenAIResponsesFinishReason.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: stop->Stop; length->MaxTokens; tool_calls->ToolCalls; null->Unknown | **Property**: prop_finishReasonMappingTotal

#### Forge.Provider.SDK.Responses.OpenAIConfig
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/OpenAIConfig.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Loads defaults; overrides from options; validates base URL | **Property**: prop_configTimeoutPositive

#### Forge.Provider.SDK.Responses.OpenAIError
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/OpenAIError.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Parsed from JSON; message extracted; type mapped | **Property**: prop_errorCodecRoundtrip

#### Forge.Provider.SDK.Responses.APITypes
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/OpenAIResponsesAPITypes.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Type constructors valid; JSON codec; nested types | **Property**: prop_apiTypeCodecRoundtrip

#### Forge.Provider.SDK.Responses.LanguageModel
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/OpenAIResponsesLanguageModel.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Model created; generates; streaming; token usage; cancellation | **Property**: prop_tokenUsageNonNegative

#### Forge.Provider.SDK.Responses.PrepareTools
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/OpenAIResponsesPrepareTools.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Tools as function defs; parameter schema; empty list | **Property**: prop_toolDefinitionValid

#### Forge.Provider.SDK.Responses.Settings
- **File**: packages/forge-core/src/provider/sdk/openai-compatible/src/responses/OpenAIResponsesSettings.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Merged with defaults; temperature [0,2]; max_tokens positive; top_p [0,1] | **Property**: prop_temperatureBounded

#### Forge.Provider.SDK.Tool.CodeInterpreter
- **File**: packages/forge-core/src/provider/sdk/.../tool/CodeInterpreter.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Tool definition correct; input schema; output parsed | **Property**: N/A

#### Forge.Provider.SDK.Tool.FileSearch
- **File**: packages/forge-core/src/provider/sdk/.../tool/FileSearch.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Tool definition correct; query param; results parsed | **Property**: N/A

#### Forge.Provider.SDK.Tool.ImageGeneration
- **File**: packages/forge-core/src/provider/sdk/.../tool/ImageGeneration.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Tool definition; prompt param; image URL returned | **Property**: N/A

#### Forge.Provider.SDK.Tool.LocalShell / WebSearch / WebSearchPreview
- **File**: packages/forge-core/src/provider/sdk/.../tool/{LocalShell,WebSearch,WebSearchPreview}.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Tool definitions correct; required params; outputs parsed | **Property**: N/A


### 4.20 PTY, Question, Scheduler

#### Forge.PTY.Index
- **File**: packages/forge-core/src/pty/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Spawns shell; captures output; sends input; resize; cleanup | **Property**: prop_ptyOutputNonLossy

#### Forge.Question.Index
- **File**: packages/forge-core/src/question/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Question asked; response received; timeout; cancelled; with choices | **Property**: prop_questionResponseInChoices

#### Forge.Scheduler.Index
- **File**: packages/forge-core/src/scheduler/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Task scheduled; executes at time; cancelled; concurrency limit; retry | **Property**: prop_schedulerFIFO

### 4.21 Server

#### Forge.Server.Error
- **File**: packages/forge-core/src/server/Error.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Error types serializable; HTTP status codes; no secrets leaked | **Property**: prop_errorStatusCodeBounded

#### Forge.Server.Event
- **File**: packages/forge-core/src/server/Event.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: SSE events formatted; stream connects; types enumerable; valid JSON | **Property**: prop_sseFormatValid

#### Forge.Server.MDNS
- **File**: packages/forge-core/src/server/MDNS.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Service advertised; discovered; conflict resolved | **Property**: N/A

#### Forge.Server.Server
- **File**: packages/forge-core/src/server/Server.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Starts; routes registered; middleware; graceful shutdown; CORS | **Property**: prop_serverHandlesAllRoutes

#### Forge.Server.Routes.Config
- **File**: packages/forge-core/src/server/routes/Config.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: GET returns current; PATCH updates; validation rejects invalid | **Property**: prop_configRouteIdempotent

#### Forge.Server.Routes.Experimental
- **File**: packages/forge-core/src/server/routes/Experimental.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Gated by flag; response shape documented | **Property**: N/A

#### Forge.Server.Routes.File
- **File**: packages/forge-core/src/server/routes/File.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: GET reads content; path traversal blocked; binary; large file streamed | **Property**: prop_fileRouteNoPathTraversal

#### Forge.Server.Routes.Global
- **File**: packages/forge-core/src/server/routes/Global.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: GET returns state; updates via SSE | **Property**: N/A

#### Forge.Server.Routes.Mcp
- **File**: packages/forge-core/src/server/routes/Mcp.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Proxy routes; tool invocation forwarded; auth passed | **Property**: N/A

#### Forge.Server.Routes.Permission
- **File**: packages/forge-core/src/server/routes/Permission.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: POST grant; POST deny; GET status | **Property**: prop_permissionRouteConsistent

#### Forge.Server.Routes.Project
- **File**: packages/forge-core/src/server/routes/Project.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: GET returns metadata; switch handled | **Property**: N/A

#### Forge.Server.Routes.Provider
- **File**: packages/forge-core/src/server/routes/Provider.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: GET lists all; switch works; auth status | **Property**: N/A

#### Forge.Server.Routes.Pty
- **File**: packages/forge-core/src/server/routes/Pty.purs | **Tests**: None | **Priority**: LOW
- **Unit**: WebSocket connection; output forwarded; input sent | **Property**: N/A

#### Forge.Server.Routes.Question
- **File**: packages/forge-core/src/server/routes/Question.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Prompt displayed; answer submitted; timeout enforced | **Property**: N/A

#### Forge.Server.Routes.Session
- **File**: packages/forge-core/src/server/routes/Session.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: POST creates; GET lists; GET by id; DELETE; POST message | **Property**: prop_sessionCRUDConsistent

#### Forge.Server.Routes.Tui
- **File**: packages/forge-core/src/server/routes/Tui.purs | **Tests**: None | **Priority**: LOW
- **Unit**: WebSocket; state synced; events forwarded | **Property**: N/A


### 4.22 Session

#### Forge.Session.Compaction
- **File**: packages/forge-core/src/session/Compaction.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Triggers at threshold; summary accurate; tool results preserved; reversible | **Property**: prop_compactionReducesTokens

#### Forge.Session.Index
- **File**: packages/forge-core/src/session/Index.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Created; loaded; saved; listed; deleted | **Property**: prop_sessionCodecRoundtrip

#### Forge.Session.Instruction
- **File**: packages/forge-core/src/session/Instruction.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: System instruction set; merged with project; includes tool defs; token count | **Property**: prop_instructionNonEmpty

#### Forge.Session.LLM
- **File**: packages/forge-core/src/session/LLM.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Stream returns chunks; tool calls trigger handler; timeout aborts; token usage | **Property**: prop_streamAlwaysTerminates, prop_tokenUsageMonotonic

#### Forge.Session.LLMTypes
- **File**: packages/forge-core/src/session/LLMTypes.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: All types constructable; codec roundtrip | **Property**: prop_llmTypeCodecRoundtrip

#### Forge.Session.Message
- **File**: packages/forge-core/src/session/Message.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Created with role; content set; metadata; serialized; parts enumerable | **Property**: prop_messageCodecRoundtrip

#### Forge.Session.MessageV2
- **File**: packages/forge-core/src/session/MessageV2.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Backward compatible V1; typed parts; metadata extended; tool use parts | **Property**: prop_v2BackwardCompatible

#### Forge.Session.Processor
- **File**: packages/forge-core/src/session/Processor.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Handles text; tool call; tool result; chains steps; max iterations | **Property**: prop_processorTerminates

#### Forge.Session.Prompt
- **File**: packages/forge-core/src/session/Prompt.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Template rendered; variables substituted; missing var handled | **Property**: prop_promptSubstitutionIdempotent

#### Forge.Session.Retry
- **File**: packages/forge-core/src/session/Retry.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Retry on transient; no retry permanent; count respected; exponential backoff | **Property**: prop_retryCountBounded, prop_backoffMonotonic

#### Forge.Session.Revert
- **File**: packages/forge-core/src/session/Revert.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Removes last turn; restores files; handles empty; handles compacted | **Property**: prop_revertReducesMessageCount

#### Forge.Session.Session
- **File**: packages/forge-core/src/session/Session.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: CRUD; persistence; concurrent access; garbage collection | **Property**: prop_sessionPersistRoundtrip

#### Forge.Session.Status
- **File**: packages/forge-core/src/session/Status.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Transitions valid; serializable; terminal states recognized | **Property**: prop_statusTransitionValid

#### Forge.Session.Summary
- **File**: packages/forge-core/src/session/Summary.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Generated from messages; length bounded; captures key actions | **Property**: prop_summaryLengthBounded

#### Forge.Session.System
- **File**: packages/forge-core/src/session/System.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Prompt assembled; includes tools; project context; permissions | **Property**: prop_systemPromptNonEmpty

#### Forge.Session.Todo
- **File**: packages/forge-core/src/session/Todo.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Items tracked; status updated; persisted across sessions | **Property**: prop_todoStatusTransitionValid


### 4.23 Share, Shell, Skill, Snapshot, Storage

#### Forge.Share.Share
- **File**: packages/forge-core/src/share/Share.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Generates URL; uploads session; access control; expiry | **Property**: prop_shareUrlValid

#### Forge.Share.ShareNext
- **File**: packages/forge-core/src/share/ShareNext.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: New API; backward compatible; handles large sessions | **Property**: prop_shareNextCodecRoundtrip

#### Forge.Shell.Shell
- **File**: packages/forge-core/src/shell/Shell.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Command executed; stdout; stderr; exit code; timeout; working dir | **Property**: prop_exitCodeBounded

#### Forge.Skill.Index
- **File**: packages/forge-core/src/skill/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Loaded from dir; by name; content returned; missing handled | **Property**: prop_skillNamesUnique

#### Forge.Skill.Skill
- **File**: packages/forge-core/src/skill/Skill.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Parsed from markdown; metadata extracted; content rendered | **Property**: prop_skillCodecRoundtrip

#### Forge.Snapshot.Index
- **File**: packages/forge-core/src/snapshot/Index.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Created from state; restored; diff computed; listed; pruned | **Property**: prop_snapshotRestoreRoundtrip

#### Forge.Storage.Storage
- **File**: packages/forge-core/src/storage/Storage.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Reads value; writes; deletes; lists keys; missing key; corrupt data | **Property**: prop_storageReadWriteRoundtrip

### 4.24 Tool (24 modules)

#### Forge.Tool.ApplyPatch
- **File**: packages/forge-core/src/tool/ApplyPatch.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Applies correctly; rejects invalid; file creation; deletion; rename | **Property**: prop_applyPatchIdempotent

#### Forge.Tool.Bash
- **File**: packages/forge-core/src/tool/Bash.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Captures stdout/stderr; timeout; missing binary; exit code; working dir | **Property**: prop_exitCodeBounded, prop_outputTruncatedAtLimit

#### Forge.Tool.Batch
- **File**: packages/forge-core/src/tool/Batch.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Multiple tools; collects results; partial failure; ordering | **Property**: prop_batchResultCountMatchesInput

#### Forge.Tool.Codesearch
- **File**: packages/forge-core/src/tool/Codesearch.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Returns matches; regex; file filter; no results | **Property**: prop_searchResultsContainQuery

#### Forge.Tool.Edit
- **File**: packages/forge-core/src/tool/Edit.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Diff applies; rejects invalid; concurrent edits; encoding; empty file | **Property**: prop_editIdempotent, prop_diffRoundtrip

#### Forge.Tool.ExternalDirectory
- **File**: packages/forge-core/src/tool/ExternalDirectory.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Access granted; path validation; symlink resolution; permission check | **Property**: prop_externalPathContained

#### Forge.Tool.Glob
- **File**: packages/forge-core/src/tool/Glob.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Pattern matches; wildcards; negation; respects ignore; no matches | **Property**: prop_globResultsExist

#### Forge.Tool.Grep
- **File**: packages/forge-core/src/tool/Grep.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Finds pattern; regex; line numbers; max results; binary files | **Property**: prop_grepResultsContainPattern

#### Forge.Tool.Invalid
- **File**: packages/forge-core/src/tool/Invalid.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Returns error; includes tool name; suggests closest match | **Property**: prop_invalidAlwaysErrors

#### Forge.Tool.Ls
- **File**: packages/forge-core/src/tool/Ls.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Lists directory; file types; empty dir; permission denied | **Property**: N/A

#### Forge.Tool.Lsp
- **File**: packages/forge-core/src/tool/Lsp.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Queries definitions; references; no server; timeout | **Property**: N/A

#### Forge.Tool.Multiedit
- **File**: packages/forge-core/src/tool/Multiedit.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Multiple edits one file; order matters; conflict; atomic | **Property**: prop_multieditAtomic

#### Forge.Tool.Plan
- **File**: packages/forge-core/src/tool/Plan.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Records plan text; stored in session; retrievable | **Property**: N/A

#### Forge.Tool.Question
- **File**: packages/forge-core/src/tool/Question.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Prompts user; receives response; timeout; default | **Property**: N/A

#### Forge.Tool.Read
- **File**: packages/forge-core/src/tool/Read.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Returns content; large file; binary; missing; line range; no path traversal | **Property**: prop_readNoPathTraversal

#### Forge.Tool.Registry
- **File**: packages/forge-core/src/tool/Registry.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: All registered; lookup by name; definition correct; custom tools; deterministic | **Property**: prop_toolNamesUnique

#### Forge.Tool.Skill
- **File**: packages/forge-core/src/tool/Skill.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Loads skill; injected into context | **Property**: N/A

#### Forge.Tool.Task
- **File**: packages/forge-core/src/tool/Task.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Spawns sub-agent; result collected; failure; timeout | **Property**: prop_taskTerminates

#### Forge.Tool.Todo
- **File**: packages/forge-core/src/tool/Todo.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Creates item; updates; lists | **Property**: N/A

#### Forge.Tool.Tool
- **File**: packages/forge-core/src/tool/Tool.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Type constructors; execution dispatched; input validated; output formatted | **Property**: prop_toolCodecRoundtrip

#### Forge.Tool.Truncation
- **File**: packages/forge-core/src/tool/Truncation.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Long output truncated; indicator added; token limit; preserves structure | **Property**: prop_truncatedOutputShorter

#### Forge.Tool.Webfetch
- **File**: packages/forge-core/src/tool/Webfetch.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Retrieves URL; timeout; 404; strips scripts; max size | **Property**: prop_webfetchOutputBounded

#### Forge.Tool.Websearch
- **File**: packages/forge-core/src/tool/Websearch.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Returns results; no results; format consistent | **Property**: prop_websearchResultCountBounded

#### Forge.Tool.Write
- **File**: packages/forge-core/src/tool/Write.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Creates file; overwrites; creates dirs; validates path; no traversal | **Property**: prop_writeReadRoundtrip


### 4.25 Util (22 modules)

#### Forge.Util.Archive
- **File**: packages/forge-core/src/util/Archive.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Compresses; decompresses; empty; large files | **Property**: prop_archiveRoundtrip

#### Forge.Util.Color
- **File**: packages/forge-core/src/util/Color.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Codes generated; disabled for no-color; 256 color support | **Property**: N/A

#### Forge.Util.Context
- **File**: packages/forge-core/src/util/Context.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Created; propagated; values accessible; isolated between requests | **Property**: prop_contextIsolation

#### Forge.Util.Defer
- **File**: packages/forge-core/src/util/Defer.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Runs at end; reverse order; handles error | **Property**: N/A

#### Forge.Util.EventLoop
- **File**: packages/forge-core/src/util/EventLoop.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Keeps process alive; exits when empty | **Property**: N/A

#### Forge.Util.Filesystem
- **File**: packages/forge-core/src/util/Filesystem.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Path join; normalize; is absolute; temp file; temp dir | **Property**: prop_normalizeIdempotent

#### Forge.Util.Fn
- **File**: packages/forge-core/src/util/Fn.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Composition; pipe; identity | **Property**: prop_composeAssociative

#### Forge.Util.Format
- **File**: packages/forge-core/src/util/Format.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Number formatting; byte formatting; duration; percentage | **Property**: prop_formatOutputNonEmpty

#### Forge.Util.IIFE
- **File**: packages/forge-core/src/util/IIFE.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Executes immediately; returns value; handles error | **Property**: N/A

#### Forge.Util.Keybind
- **File**: packages/forge-core/src/util/Keybind.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Parsed from string; matches event; modifier keys; conflict detection | **Property**: prop_keybindParseRoundtrip

#### Forge.Util.Lazy
- **File**: packages/forge-core/src/util/Lazy.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Computed once; memoized; handles error | **Property**: prop_lazyComputesOnce

#### Forge.Util.Locale
- **File**: packages/forge-core/src/util/Locale.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Detected; fallback to en; formatting applied | **Property**: N/A

#### Forge.Util.Lock
- **File**: packages/forge-core/src/util/Lock.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Acquired; released; prevents concurrent; timeout; reentrant check | **Property**: prop_lockMutualExclusion

#### Forge.Util.Log
- **File**: packages/forge-core/src/util/Log.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Writes message; level filtering; structured format; destination | **Property**: N/A

#### Forge.Util.NotImplemented
- **File**: packages/forge-core/src/util/NotImplemented.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Throws; includes feature name | **Property**: N/A

#### Forge.Util.Queue
- **File**: packages/forge-core/src/util/Queue.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Enqueue/dequeue; FIFO; empty check; bounded; blocks on full | **Property**: prop_queueFIFO

#### Forge.Util.RPC
- **File**: packages/forge-core/src/util/RPC.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Sends request; receives response; timeout; error handling | **Property**: prop_rpcRequestResponsePaired

#### Forge.Util.Scrap
- **File**: packages/forge-core/src/util/Scrap.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Stores temp data; clears | **Property**: N/A

#### Forge.Util.Signal
- **File**: packages/forge-core/src/util/Signal.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Subscription; emission; cleanup | **Property**: N/A

#### Forge.Util.Slug
- **File**: packages/forge-core/src/util/Slug.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Generated from string; URL-safe; unicode; empty string | **Property**: prop_slugUrlSafe

#### Forge.Util.Timeout
- **File**: packages/forge-core/src/util/Timeout.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Fires after duration; cancellable; zero; negative as zero | **Property**: prop_timeoutDurationPositive

#### Forge.Util.Token
- **File**: packages/forge-core/src/util/Token.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Count estimated; different encodings; empty; unicode | **Property**: prop_tokenCountNonNegative, prop_tokenCountMonotonicWithLength

#### Forge.Util.Wildcard
- **File**: packages/forge-core/src/util/Wildcard.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Star matches any; question matches single; escaping; empty | **Property**: prop_wildcardStarMatchesAll

### 4.26 Worktree, Index

#### Forge.Worktree.Index
- **File**: packages/forge-core/src/worktree/Index.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Created; listed; removed; isolated from main; branch tracked | **Property**: prop_worktreeIsolation

#### Forge.Index
- **File**: packages/forge-core/src/Index.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Top-level re-exports | **Property**: N/A

---


## 5. app (70 modules)

### 5.1 Core

#### App.App
- **File**: packages/app/src/App.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: App component renders; routes initialized; error boundary catches | **Property**: N/A

#### App.AppM
- **File**: packages/app/src/AppM.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: App monad runs effects; context provided; error propagation | **Property**: N/A

### 5.2 Voice

#### App.Voice.AudioVisualizer
- **File**: packages/app/src/Voice/AudioVisualizer.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Visualizer renders; frequency data displayed; stops on unmount | **Property**: N/A

#### App.Voice.MicrophoneButton
- **File**: packages/app/src/Voice/MicrophoneButton.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Button toggles recording; visual feedback; permission request | **Property**: N/A

#### App.Voice.TranscriptView
- **File**: packages/app/src/Voice/TranscriptView.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Transcript displayed; updates live; scrolls to bottom | **Property**: N/A

#### App.Voice.VoiceSelector
- **File**: packages/app/src/Voice/VoiceSelector.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Voice list populated; selection persists; preview plays | **Property**: N/A

### 5.3 Addons

#### App.Addons.Serialize
- **File**: packages/app/src/addons/Serialize.purs | **Tests**: Exists (Serialize.Spec.purs) | **Priority**: HIGH
- **Unit**: Serialization roundtrip; handles nested objects; handles arrays | **Property**: prop_serializeRoundtrip

### 5.4 Components

#### App.Components.AlertSystem
- **File**: packages/app/src/components/AlertSystem.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Alert shown; auto-dismiss; queue management; severity levels | **Property**: N/A

#### App.Components.Balance.BalanceTracker
- **File**: packages/app/src/components/Balance/BalanceTracker.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Balance displayed; updates on usage; low balance warning | **Property**: prop_balanceNonNegative

#### App.Components.Balance.CountdownTimer
- **File**: packages/app/src/components/Balance/CountdownTimer.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Timer counts down; reaches zero; formatted display | **Property**: prop_countdownMonotonic

#### App.Components.Balance.DiemTracker
- **File**: packages/app/src/components/Balance/DiemTracker.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Diem balance tracked; conversion displayed | **Property**: N/A

#### App.Components.CodeSelection
- **File**: packages/app/src/components/CodeSelection.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Code block selected; range highlighted; copy works | **Property**: N/A

#### App.Components.CommandPalette
- **File**: packages/app/src/components/CommandPalette.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Opens on shortcut; search filters; command executes | **Property**: N/A

#### App.Components.Dashboard
- **File**: packages/app/src/components/Dashboard.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Dashboard renders; session list; quick actions | **Property**: N/A

#### App.Components.DiffViewer
- **File**: packages/app/src/components/DiffViewer.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Diff displayed; added/removed highlighted; line numbers | **Property**: N/A

#### App.Components.FileContextView
- **File**: packages/app/src/components/FileContextView.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: File context shown; syntax highlighting; line numbers | **Property**: N/A

#### App.Components.HelpOverlay
- **File**: packages/app/src/components/HelpOverlay.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Overlay shown; keybindings listed; dismissable | **Property**: N/A

#### App.Components.KeyboardNavigation
- **File**: packages/app/src/components/KeyboardNavigation.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Arrow keys navigate; Enter selects; Escape cancels | **Property**: N/A

#### App.Components.Proof.ProofPanel
- **File**: packages/app/src/components/Proof/ProofPanel.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Proof panel renders; proof status shown; verification result | **Property**: N/A

#### App.Components.Settings.SettingsPanel
- **File**: packages/app/src/components/Settings/SettingsPanel.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Settings displayed; changes saved; reset to defaults | **Property**: N/A

#### App.Components.Sidebar
- **File**: packages/app/src/components/Sidebar.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Sidebar renders; session list; toggle collapse | **Property**: N/A

#### App.Components.TerminalEmbed
- **File**: packages/app/src/components/TerminalEmbed.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Terminal renders; output displayed; input forwarded | **Property**: N/A

#### App.Components.TokenUsageChart
- **File**: packages/app/src/components/TokenUsageChart.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Chart renders; data plotted; tooltips work | **Property**: N/A

#### App.Components.Session.SessionPanel
- **File**: packages/app/src/components/session/SessionPanel.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Session messages rendered; streaming shown; tool results; input area | **Property**: N/A


### 5.5 Context (20 modules)

#### App.Context.Bridge
- **File**: packages/app/src/context/Bridge.purs | **Tests**: Exists (BridgeSpec) | **Priority**: HIGH
- **Unit**: Bridge connection; message send/receive; reconnect; state sync | **Property**: N/A

#### App.Context.Command
- **File**: packages/app/src/context/Command.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Command context provided; dispatches | **Property**: N/A

#### App.Context.Comments
- **File**: packages/app/src/context/Comments.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Comments loaded; displayed inline; submit new | **Property**: N/A

#### App.Context.File
- **File**: packages/app/src/context/File.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: File context loaded; syntax detection; content provided | **Property**: N/A

#### App.Context.GlobalSDK / GlobalSync / Highlights / Language / Layout / LayoutScroll
- **File**: packages/app/src/context/{GlobalSDK,GlobalSync,Highlights,Language,Layout,LayoutScroll}.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Context providers initialized; values propagated; cleanup on unmount | **Property**: N/A

#### App.Context.Local / Models / Notification / Permission / Platform / Prompt
- **File**: packages/app/src/context/{Local,Models,Notification,Permission,Platform,Prompt}.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Context values correct; updates propagate; default values | **Property**: N/A

#### App.Context.SDK / Server / Settings / Sync / Terminal / Types
- **File**: packages/app/src/context/{SDK,Server,Settings,Sync,Terminal,Types}.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Type definitions valid; context integration correct | **Property**: N/A

### 5.6 Hooks

#### App.Hooks.UseProviders
- **File**: packages/app/src/hooks/UseProviders.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Provider list returned; updates on change; loading state | **Property**: N/A

#### App.Hooks.UseVoice
- **File**: packages/app/src/hooks/UseVoice.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Voice recording starts/stops; transcript returned; error handled | **Property**: N/A

### 5.7 i18n

#### App.I18n.En / I18n / Types
- **File**: packages/app/src/i18n/{En,I18n,Types}.purs | **Tests**: None | **Priority**: LOW
- **Unit**: All keys present; translation lookup works; fallback to English | **Property**: prop_allKeysHaveTranslation

### 5.8 Pages

#### App.Pages.DirectoryLayout / Error / Home / Layout / Session / Voice
- **File**: packages/app/src/pages/{DirectoryLayout,Error,Home,Layout,Session,Voice}.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Page renders; navigation works; error page shows message | **Property**: N/A

### 5.9 Utils

#### App.Utils.Agent / Base64 / Dom / Id / Maybe / Perf / Persist / Prompt / Same / SolidDnd / Sound / Speech / Worktree
- **File**: packages/app/src/utils/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Utility functions correct; edge cases handled; type safety | **Property**: prop_base64Roundtrip, prop_idUnique

### 5.10 Existing Tests (app)

| Test File | Status |
|---|---|
| Serialize.Spec.purs | EXISTS - addon serialization roundtrip |
| BridgeSpec.purs | EXISTS - bridge API integration |
| WebSocketSpec.purs | EXISTS - WebSocket FFI |
| RouterSpec.purs | EXISTS - routing logic |
| AppStateSpec.purs | EXISTS - app state management |
| BalanceSpec.purs | EXISTS - balance tracking |
| ReducerSpec.purs | EXISTS - state reducer logic |
| PrismSpec.purs | EXISTS - theme prism parsing |
| CurrencySpec.purs | EXISTS - currency formatting |
| TimeSpec.purs | EXISTS - time formatting |
| WebSocket.ClientSpec.purs | EXISTS - WebSocket client |

---


## 6. ui (88 modules)

### 6.1 Components (51 modules)

#### UI.Components.Accordion
- **File**: packages/ui/src/components/Accordion.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Expands/collapses; single/multi mode; keyboard accessible | **Property**: N/A

#### UI.Components.Avatar
- **File**: packages/ui/src/components/Avatar.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Renders image; fallback initials; size variants | **Property**: N/A

#### UI.Components.BasicTool
- **File**: packages/ui/src/components/BasicTool.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Tool result rendered; expandable; copy button | **Property**: N/A

#### UI.Components.Button
- **File**: packages/ui/src/components/Button.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Click handler; disabled state; loading state; variants | **Property**: N/A

#### UI.Components.Card
- **File**: packages/ui/src/components/Card.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Renders children; header/footer slots; hover effect | **Property**: N/A

#### UI.Components.Checkbox / Code / Collapsible / Dialog
- **File**: packages/ui/src/components/{Checkbox,Code,Collapsible,Dialog}.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Toggle state; syntax highlighting; expand/collapse animation; modal overlay | **Property**: N/A

#### UI.Components.Diff / DiffChanges / DiffSsr
- **File**: packages/ui/src/components/{Diff,DiffChanges,DiffSsr}.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Diff rendered correctly; additions green; deletions red; SSR compatible | **Property**: N/A

#### UI.Components.DropdownMenu / Favicon / FileIcon / Font
- **File**: packages/ui/src/components/{DropdownMenu,Favicon,FileIcon,Font}.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Menu opens; favicon loads; file icons mapped; font loaded | **Property**: N/A

#### UI.Components.HoverCard / Icon / IconButton / ImagePreview / InlineInput
- **File**: packages/ui/src/components/{HoverCard,Icon,IconButton,ImagePreview,InlineInput}.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Hover triggers; icon renders; click handler; image loads; input editable | **Property**: N/A

#### UI.Components.Keybind / LineComment / List / Logo / Markdown
- **File**: packages/ui/src/components/{Keybind,LineComment,List,Logo,Markdown}.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Keybind displayed; comment positioned; list items rendered; markdown parsed | **Property**: N/A

#### UI.Components.MessageNav / MessagePart / MessagePart.Component / MessagePart.Registry / MessagePart.Types
- **File**: packages/ui/src/components/MessageNav.purs and MessagePart/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Navigation between messages; part rendering; component registry lookup; type safety | **Property**: N/A

#### UI.Components.Popover / ProgressCircle / ProviderIcon / RadioGroup / ResizeHandle
- **File**: packages/ui/src/components/{Popover,ProgressCircle,ProviderIcon,RadioGroup,ResizeHandle}.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Popover positions; progress animates; provider icon mapped; radio selection; resize drag | **Property**: N/A

#### UI.Components.Select / SessionReview / SessionTurn / SessionTurn.Component / SessionTurn.Status / SessionTurn.Types
- **File**: packages/ui/src/components/Select.purs and SessionTurn/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Select opens/closes; session turn rendered; status indicators; type definitions | **Property**: N/A

#### UI.Components.Spinner / StickyAccordionHeader / Switch / Tabs / Tag / TextField / Toast / Tooltip / Typewriter
- **File**: packages/ui/src/components/{Spinner,StickyAccordionHeader,Switch,Tabs,Tag,TextField,Toast,Tooltip,Typewriter}.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Animation; sticky behavior; toggle; tab switch; tag display; input validation; toast auto-dismiss; tooltip position; typewriter effect | **Property**: N/A

### 6.2 Context (9 modules)

#### UI.Context.Code / Data / Dialog / Diff / Helper / I18n / Index / Marked / WorkerPool
- **File**: packages/ui/src/context/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Context providers; state management; worker pool sizing; markdown parsing | **Property**: N/A

### 6.3 Hooks (3 modules)

#### UI.Hooks.CreateAutoScroll / Index / UseFilteredList
- **File**: packages/ui/src/hooks/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Auto-scroll triggers; filtered list updates on input; debounce | **Property**: prop_filteredListSubsetOfFull

### 6.4 i18n (16 modules)

#### UI.I18n.{Ar,Br,Da,De,En,Eo,Es,Fr,Ja,Ko,No,Pl,Ru,Th,Zh,Zht}
- **File**: packages/ui/src/i18n/*.purs | **Tests**: None | **Priority**: LOW
- **Unit**: All keys present in each locale; no missing translations vs En baseline | **Property**: prop_allLocalesHaveAllKeys

### 6.5 Pierre (3 modules)

#### UI.Pierre.Index / Types / Worker
- **File**: packages/ui/src/pierre/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Pierre worker initializes; processes messages; types valid | **Property**: N/A

### 6.6 Theme (8 modules)

#### UI.Theme.Color / Context / Contrast / Index / Loader / Palette / Resolve / Types
- **File**: packages/ui/src/theme/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Color values valid; contrast ratios WCAG compliant; theme loaded; palette generated; CSS vars resolved | **Property**: prop_contrastRatioMinimum(4.5)

---


## 7. forge/server (61 source modules + 11 types + 4 util)

### 7.1 Plugin (3 modules)

#### Forge.Plugin.FFI.Plugin
- **File**: packages/forge/src/plugin/src/Bridge/FFI/Forge/Plugin.purs | **Tests**: Exists (PluginSpec) | **Priority**: HIGH
- **Unit**: Plugin loaded via FFI; methods callable; error handling | **Property**: N/A

#### Forge.Plugin.FFI.WebSocket.Client
- **File**: packages/forge/src/plugin/src/Bridge/FFI/WebSocket/Client.purs | **Tests**: Exists (ClientSpec) | **Priority**: HIGH
- **Unit**: WebSocket connects; messages sent/received; reconnect | **Property**: N/A

#### Forge.Plugin.Main
- **File**: packages/forge/src/plugin/src/Forge/Plugin/Main.purs | **Tests**: Exists (MainSpec) | **Priority**: HIGH
- **Unit**: Plugin entry point; initialization; cleanup | **Property**: N/A

### 7.2 Server (46 modules)

#### Bridge.Auth.JWT / Origin / RBAC / RateLimit / Session
- **File**: packages/forge/src/server/src/Bridge/Auth/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: JWT validated; origin checked; RBAC enforced; rate limited; session tracked | **Property**: prop_jwtRoundtrip, prop_rbacNoEscalation

#### Bridge.Config
- **File**: packages/forge/src/server/src/Bridge/Config.purs | **Tests**: Exists (ConfigSpec) | **Priority**: HIGH
- **Unit**: Config loaded; validated; defaults applied | **Property**: prop_configCodecRoundtrip

#### Bridge.Database.Sync
- **File**: packages/forge/src/server/src/Bridge/Database/Sync.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Database syncs; conflict resolution; offline support | **Property**: N/A

#### Bridge.Error.Retry / Taxonomy
- **File**: packages/forge/src/server/src/Bridge/Error/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Retry logic; error classification; taxonomy covers all cases | **Property**: prop_retryBackoffMonotonic

#### Bridge.FFI.Forge.SDK
- **File**: packages/forge/src/server/src/Bridge/FFI/Forge/SDK.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: SDK methods callable; types bridge correctly; errors propagated | **Property**: N/A

#### Bridge.FFI.Haskell.Analytics / Database
- **File**: packages/forge/src/server/src/Bridge/FFI/Haskell/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Haskell FFI calls succeed; data marshalled; errors caught | **Property**: N/A

#### Bridge.FFI.Node.Database / Express / Fetch / FileContext / Handlers / Http / Pino / Process / Terminal / WebSearch / WebSocket
- **File**: packages/forge/src/server/src/Bridge/FFI/Node/*.purs | **Tests**: Exists (multiple specs) | **Priority**: HIGH
- **Unit**: Node FFI bindings correct; null safety; type coercion; exception handling | **Property**: N/A

#### Bridge.Forge.Client / Events
- **File**: packages/forge/src/server/src/Bridge/Forge/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Client connects; events dispatched; error handling | **Property**: N/A

#### Bridge.Lean.Proxy
- **File**: packages/forge/src/server/src/Bridge/Lean/Proxy.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Lean proxy forwards; type checking; timeout | **Property**: N/A

#### Bridge.Logging.Structured
- **File**: packages/forge/src/server/src/Bridge/Logging/Structured.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Structured logging; JSON format; log levels | **Property**: N/A

#### Bridge.Main
- **File**: packages/forge/src/server/src/Bridge/Main.purs | **Tests**: Exists (MainSpec) | **Priority**: HIGH
- **Unit**: Server starts; routes registered; graceful shutdown | **Property**: N/A

#### Bridge.Notifications.Service
- **File**: packages/forge/src/server/src/Bridge/Notifications/Service.purs | **Tests**: Exists (ServiceSpec) | **Priority**: MEDIUM
- **Unit**: Notification sent; queued; rate limited | **Property**: N/A

#### Bridge.Security.Headers / Validation
- **File**: packages/forge/src/server/src/Bridge/Security/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Security headers set; input validated; XSS prevented | **Property**: prop_headersAlwaysSet

#### Bridge.Server
- **File**: packages/forge/src/server/src/Bridge/Server.purs | **Tests**: Exists (ServerSpec) | **Priority**: HIGH
- **Unit**: Server lifecycle; middleware chain; error handling | **Property**: N/A

#### Bridge.State.Store
- **File**: packages/forge/src/server/src/Bridge/State/Store.purs | **Tests**: Exists (StoreSpec) | **Priority**: HIGH
- **Unit**: State updated; subscribers notified; consistent reads | **Property**: prop_storeReducerCommutative

#### Bridge.Tracing.OpenTelemetry
- **File**: packages/forge/src/server/src/Bridge/Tracing/OpenTelemetry.purs | **Tests**: None | **Priority**: LOW
- **Unit**: Traces created; spans nested; exported | **Property**: N/A

#### Bridge.Utils.ErrorHandling / Json / Metrics / Time / Validation
- **File**: packages/forge/src/server/src/Bridge/Utils/*.purs | **Tests**: Exists (multiple specs) | **Priority**: HIGH
- **Unit**: Error formatted; JSON parsed/serialized; metrics recorded; time formatted; input validated | **Property**: prop_jsonRoundtrip, prop_validationIdempotent

#### Bridge.Venice.Client / RateLimiter
- **File**: packages/forge/src/server/src/Bridge/Venice/*.purs | **Tests**: Exists (RateLimiterSpec) | **Priority**: HIGH
- **Unit**: Venice API called; rate limits enforced; token bucket algorithm | **Property**: prop_rateLimiterNeverExceedsBurst

#### Bridge.WebSocket.Handlers / Manager
- **File**: packages/forge/src/server/src/Bridge/WebSocket/*.purs | **Tests**: Exists (ManagerSpec) | **Priority**: HIGH
- **Unit**: WebSocket lifecycle; message routing; connection pool | **Property**: N/A

### 7.3 Storage -- Haskell (15 modules)

#### Bridge.Database / Database.Operations / Database.Schema
- **File**: packages/forge/src/storage/src/Bridge/Database*.hs | **Tests**: Exists (multiple specs) | **Priority**: HIGH
- **Unit**: CRUD operations; schema migrations; query optimization | **Property**: prop_databaseRoundtrip

#### Bridge.Alerts.System / Auth.Encryption / Backup.Scheduler / Backup.Verification
- **File**: packages/forge/src/storage/src/Bridge/*.hs | **Tests**: Exists (BackupSpec, SecuritySpec) | **Priority**: HIGH
- **Unit**: Alert triggers; encryption roundtrip; backup scheduled; verified | **Property**: prop_encryptionRoundtrip

#### Bridge.Error.CircuitBreaker / Metrics.Prometheus / Performance.Benchmarks / Security.Secrets
- **File**: packages/forge/src/storage/src/Bridge/*.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Circuit breaker trips; metrics exported; benchmarks pass; secrets never logged | **Property**: prop_circuitBreakerTrips

### 7.4 Analytics -- Haskell (3 modules)

#### Bridge.Analytics / Analytics.DuckDB / Analytics.Queries
- **File**: packages/forge/src/storage/analytics/src/Bridge/*.hs | **Tests**: Exists (4 specs) | **Priority**: HIGH
- **Unit**: Analytics recorded; DuckDB queries; aggregation correct | **Property**: prop_queryResultsConsistent

### 7.5 Types (11 modules)

#### Forge.Types / Types.Config / Types.File / Types.Message / Types.Permission / Types.Provider / Types.Session / Types.SessionStatus / Types.State / Types.Storage / Types.Tool
- **File**: packages/forge/src/types/src/Forge/Types*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: All type constructors valid; JSON codecs roundtrip; backward compatible | **Property**: prop_allTypesCodecRoundtrip

### 7.6 Validator -- Haskell (4 modules)

#### Forge.Validator.BannedConstructs / FileReading / Main / TypeEscapes
- **File**: packages/forge/src/util/src/Forge/Validator/*.hs | **Tests**: Exists (RulesSpec, ValidatorSpec) | **Priority**: HIGH
- **Unit**: Banned constructs detected; file reading violations caught; type escapes flagged | **Property**: prop_validatorNeverFalseNegative

### 7.7 Existing Tests (forge)

| Test File | Status |
|---|---|
| Bridge/ConfigSpec.purs | EXISTS |
| Bridge/E2E/DatabaseSpec.purs | EXISTS |
| Bridge/E2E/VeniceSpec.purs | EXISTS |
| Bridge/E2E/WebSocketSpec.purs | EXISTS |
| Bridge/E2E/forgeSpec.purs | EXISTS |
| Bridge/FFI/Node/*.Spec.purs (6 files) | EXISTS |
| Bridge/Integration/FFISpec.purs | EXISTS |
| Bridge/Integration/StateSyncSpec.purs | EXISTS |
| Bridge/MainSpec.purs | EXISTS |
| Bridge/Notifications/ServiceSpec.purs | EXISTS |
| Bridge/Protocol/JsonRpcSpec.purs | EXISTS |
| Bridge/ServerSpec.purs | EXISTS |
| Bridge/State/StoreSpec.purs | EXISTS |
| Bridge/Utils/*.Spec.purs (5 files) | EXISTS |
| Bridge/Venice/RateLimiterSpec.purs | EXISTS |
| Bridge/WebSocket/ManagerSpec.purs | EXISTS |
| storage/Bridge/*.Spec.hs (7 files) | EXISTS |
| analytics/Bridge/*.Spec.hs (4 files) | EXISTS |
| forge-core/test/*.Spec.hs (3 files) | EXISTS |

---


## 8. enterprise (18 modules)

### 8.1 Core (2 PureScript modules)

#### Render.Client
- **File**: packages/enterprise/src/Render/Client.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Client connects to gateway; requests routed; auth forwarded | **Property**: N/A

#### Render.Types
- **File**: packages/enterprise/src/Render/Types.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: All types constructable; codec roundtrips | **Property**: prop_enterpriseTypeCodecRoundtrip

### 8.2 Billing

#### Render.Billing.NVXT
- **File**: packages/enterprise/src/billing/src/Render/Billing/NVXT.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: NVXT billing calculated; usage metered; invoice generated; credit applied | **Property**: prop_billingNonNegative, prop_billingAccumulates

### 8.3 CAS

#### Render.CAS.Client
- **File**: packages/enterprise/src/cas/src/Render/CAS/Client.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: CAS store; CAS retrieve by hash; hash collision handling; deduplication | **Property**: prop_casHashDeterministic, prop_casRoundtrip

### 8.4 ClickHouse

#### Render.ClickHouse.Client
- **File**: packages/enterprise/src/clickhouse/src/Render/ClickHouse/Client.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Query executes; results parsed; connection pooled; timeout | **Property**: N/A

### 8.5 Compliance

#### Render.Compliance.AuditTrail
- **File**: packages/enterprise/src/compliance/src/Render/Compliance/AuditTrail.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Events logged; trail immutable; export formats; retention policy | **Property**: prop_auditTrailAppendOnly, prop_auditTrailComplete

### 8.6 Core Storage

#### Render.Core.Share / Storage
- **File**: packages/enterprise/src/core/src/Render/Core/*.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Share creates link; storage CRUD; encryption at rest; access control | **Property**: prop_storageEncryptionRoundtrip

### 8.7 Gateway (8 modules)

#### Render.Gateway.Backend
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/Backend.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Backend health check; load balancing; failover; connection pool | **Property**: prop_loadBalancingDistribution

#### Render.Gateway.Capacity.Queueing
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/Capacity/Queueing.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Request queued; dequeued FIFO; overflow rejected; priority queue | **Property**: prop_queueFIFO, prop_queueBounded

#### Render.Gateway.ClickHouse.Schema
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/ClickHouse/Schema.hs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Schema created; migrations applied; backward compatible | **Property**: N/A

#### Render.Gateway.Core
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/Core.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Core routing; middleware chain; error handling; metrics | **Property**: N/A

#### Render.Gateway.STM.CircuitBreaker
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/STM/CircuitBreaker.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Closed state allows; trips on failure threshold; half-open test; reset | **Property**: prop_circuitBreakerStateValid

#### Render.Gateway.STM.Clock
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/STM/Clock.hs | **Tests**: None | **Priority**: LOW
- **Unit**: Clock reads current time; monotonic; resolution | **Property**: prop_clockMonotonic

#### Render.Gateway.STM.Queue
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/STM/Queue.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: STM queue enqueue/dequeue; bounded; blocks on full; concurrent safe | **Property**: prop_stmQueueLinearizable

#### Render.Gateway.STM.RateLimiter
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/STM/RateLimiter.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Token bucket; refill rate; burst capacity; distributed rate limit | **Property**: prop_rateLimiterTokenBounded

#### Render.Gateway.Server
- **File**: packages/enterprise/src/gateway/src/Render/Gateway/Server.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Server starts; TLS; graceful shutdown; health endpoint | **Property**: N/A

#### Render.Gateway.Main
- **File**: packages/enterprise/src/gateway/app/Main.hs | **Tests**: None | **Priority**: HIGH
- **Unit**: Entry point; config loaded; server started; signal handling | **Property**: N/A

---


## 9. console (131 modules)

### 9.1 Core (16 modules)

#### Console.Core.Account / Actor / Context / Identifier / Key / Provider / Workspace
- **File**: packages/console/core/src/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Account CRUD; actor resolution; context propagation; identifier validation; key management; provider config; workspace lifecycle | **Property**: prop_identifierValid, prop_accountCodecRoundtrip

#### Console.Core.Drizzle.Database
- **File**: packages/console/core/src/drizzle/Database.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Database connection; query execution; transaction support; migration | **Property**: N/A

#### Console.Core.Schema.Account / Auth / Billing / Key / Model / Provider / Types / User / Workspace
- **File**: packages/console/core/src/schema/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Schema definitions valid; relations correct; indexes; constraints | **Property**: prop_schemaCodecRoundtrip

#### Console.Core.Util.Date / Fn / Log / Memo / Price
- **File**: packages/console/core/src/util/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Date formatting; utility functions; logging; memoization; price calculation | **Property**: prop_priceNonNegative, prop_memoConsistent

### 9.2 App Core (8 modules)

#### Console.App / Config / EntryClient / EntryServer / FFI.SolidStart / Meta / Middleware / Router
- **File**: packages/console/app/src/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: App renders; config loaded; SSR hydration; middleware chain; routing | **Property**: N/A

### 9.3 Sidepanel (3 modules)

#### Console.Sidepanel.FFI.DateTime / Utils.Currency / Utils.Time
- **File**: packages/console/app/src/Sidepanel/*.purs | **Tests**: Exists (CurrencySpec, TimeSpec) | **Priority**: MEDIUM
- **Unit**: DateTime FFI; currency formatting; time formatting | **Property**: prop_currencyFormatRoundtrip

### 9.4 Components (10 modules)

#### Console.Component.Dropdown / EmailSignup / Faq / Footer / Header / Icon / Legal / Modal / Spotlight
- **File**: packages/console/app/src/component/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Components render; interaction works; responsive layout | **Property**: N/A

### 9.5 Context (3 modules)

#### Console.Context.Auth / AuthSession / AuthWithActor
- **File**: packages/console/app/src/context/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Auth state managed; session tracked; actor resolved | **Property**: N/A

### 9.6 Routes (50+ modules)

#### Console.Routes.Index / NotFound / Discord / Temp / UserMenu
- **File**: packages/console/app/src/routes/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Pages render; navigation; 404 handling | **Property**: N/A

#### Console.Routes.Auth.Authorize / Callback / Index / Logout / Status
- **File**: packages/console/app/src/routes/auth/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: OAuth flow; callback handling; logout; status check | **Property**: N/A

#### Console.Routes.Bench.Detail / Index / Submission
- **File**: packages/console/app/src/routes/bench/*.purs | **Tests**: None | **Priority**: MEDIUM
- **Unit**: Benchmark display; submission form; detail view | **Property**: N/A

#### Console.Routes.Black.Common / Index / Workspace / Subscribe.Plan
- **File**: packages/console/app/src/routes/black/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Black tier pages; workspace management; subscription plans | **Property**: N/A

#### Console.Routes.Workspace.Common + 14 sub-routes
- **File**: packages/console/app/src/routes/workspace/**/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Workspace dashboard; billing; keys; members; settings; graphs; models; providers | **Property**: N/A

#### Console.Routes.Stripe.Webhook.{Charge,Checkout,Customer,Invoice,Main,Subscription,Types,Webhook}
- **File**: packages/console/app/src/routes/stripe/**/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: Webhook signature verified; charge processed; checkout completed; subscription lifecycle | **Property**: prop_webhookSignatureValid

### 9.7 Omega (API Gateway -- 26 modules)

#### Console.Omega.Index / Handler / Handler.Auth / Handler.Cost / Handler.Main / Handler.Provider / Handler.Reload / Handler.Types / Handler.Validation
- **File**: packages/console/app/src/routes/omega/util/Handler*.purs | **Tests**: Exists (HandlerHelpersSpec, HandlerProviderSpec) | **Priority**: HIGH
- **Unit**: Request handling; auth validation; cost calculation; provider routing; reloading; input validation | **Property**: prop_costCalculationCorrect

#### Console.Omega.DataDumper / Error / Logger / MessageEncryption / MessageEncryptionHelpers / RateLimiter / StickyProviderTracker / TrialLimiter
- **File**: packages/console/app/src/routes/omega/util/*.purs | **Tests**: Exists (multiple specs) | **Priority**: HIGH
- **Unit**: Data export; error handling; structured logging; message encryption; rate limiting; provider stickiness; trial limits | **Property**: prop_encryptionRoundtrip, prop_rateLimiterBounded

#### Console.Omega.Provider.{Anthropic,Google,OpenAI,OpenAICompatible} + sub-modules (Chunk/Request/Response)
- **File**: packages/console/app/src/routes/omega/util/provider/**/*.purs | **Tests**: Exists (14 specs) | **Priority**: HIGH
- **Unit**: Provider request formatted; response parsed; chunk assembled; usage extracted | **Property**: prop_requestFormatValid, prop_responseParseComplete

#### Console.Omega.V1.ChatCompletions / Messages / ModelDetail / Models / Responses
- **File**: packages/console/app/src/routes/omega/v1/*.purs | **Tests**: None | **Priority**: HIGH
- **Unit**: API endpoints; request validation; response format; streaming; model listing | **Property**: N/A

### 9.8 Existing Tests (console)

| Test File | Status |
|---|---|
| AuthSpec.purs | EXISTS |
| CostSpec.purs | EXISTS |
| DataDumperSpec.purs | EXISTS |
| ErrorSpec.purs | EXISTS |
| HandlerHelpersSpec.purs | EXISTS |
| HandlerProviderSpec.purs | EXISTS |
| LoggerSpec.purs | EXISTS |
| MessageEncryption*.purs (2 files) | EXISTS |
| OpenAIHelperSpec.purs | EXISTS |
| ProviderHelpersSpec.purs | EXISTS |
| ProviderSpec.purs | EXISTS |
| RateLimiterSpec.purs | EXISTS |
| ReloadSpec.purs | EXISTS |
| StickyProviderTrackerSpec.purs | EXISTS |
| TrialLimiterSpec.purs | EXISTS |
| ValidationSpec.purs | EXISTS |
| formatter/Currency*.purs (3 files) | EXISTS |
| provider/*Spec.purs (14 files) | EXISTS |
| ErrorHandlingIntegrationSpec.purs | EXISTS |
| HandlerMainIntegrationSpec.purs | EXISTS |

---


## 10. opencode TypeScript (157 source modules, 56 test files)

### 10.1 Tested Modules (56 test files)

| Test File | Module Tested | Status |
|---|---|---|
| acp/agent-interface.test.ts | acp/agent.ts | EXISTS |
| acp/event-subscription.test.ts | acp/session.ts | EXISTS |
| agent/agent.test.ts | agent/agent.ts | EXISTS |
| bun.test.ts | bun/index.ts | EXISTS |
| cli/github-action.test.ts | cli/cmd/github.ts | EXISTS |
| cli/github-remote.test.ts | cli/cmd/github.ts | EXISTS |
| cli/tui/transcript.test.ts | cli/cmd/tui/util/transcript.ts | EXISTS |
| config/agent-color.test.ts | config/config.ts | EXISTS |
| config/config.test.ts | config/config.ts | EXISTS |
| config/markdown.test.ts | config/markdown.ts | EXISTS |
| file/ignore.test.ts | file/ignore.ts | EXISTS |
| file/path-traversal.test.ts | file/index.ts | EXISTS |
| ide/ide.test.ts | ide/index.ts | EXISTS |
| keybind.test.ts | util/keybind.ts | EXISTS |
| lsp/client.test.ts | lsp/client.ts | EXISTS |
| mcp/headers.test.ts | mcp/index.ts | EXISTS |
| mcp/oauth-browser.test.ts | mcp/oauth-callback.ts | EXISTS |
| patch/patch.test.ts | patch/index.ts | EXISTS |
| permission-task.test.ts | permission/index.ts | EXISTS |
| permission/arity.test.ts | permission/arity.ts | EXISTS |
| permission/next.test.ts | permission/next.ts | EXISTS |
| plugin/codex.test.ts | plugin/codex.ts | EXISTS |
| project/project.test.ts | project/project.ts | EXISTS |
| provider/amazon-bedrock.test.ts | provider/provider.ts | EXISTS |
| provider/gitlab-duo.test.ts | provider/provider.ts | EXISTS |
| provider/provider.test.ts | provider/provider.ts | EXISTS |
| provider/transform.test.ts | provider/transform.ts | EXISTS |
| question/question.test.ts | question/index.ts | EXISTS |
| scheduler.test.ts | scheduler/index.ts | EXISTS |
| server/session-list.test.ts | server/routes/session.ts | EXISTS |
| server/session-select.test.ts | server/routes/session.ts | EXISTS |
| session/compaction.test.ts | session/compaction.ts | EXISTS |
| session/instruction.test.ts | session/instruction.ts | EXISTS |
| session/llm.test.ts | session/llm.ts | EXISTS |
| session/message-v2.test.ts | session/message-v2.ts | EXISTS |
| session/retry.test.ts | session/retry.ts | EXISTS |
| session/revert-compact.test.ts | session/revert.ts | EXISTS |
| session/session.test.ts | session/index.ts | EXISTS |
| skill/skill.test.ts | skill/index.ts | EXISTS |
| snapshot/snapshot.test.ts | snapshot/index.ts | EXISTS |
| tool/apply_patch.test.ts | tool/apply_patch.ts | EXISTS |
| tool/bash.test.ts | tool/bash.ts | EXISTS |
| tool/external-directory.test.ts | tool/external-directory.ts | EXISTS |
| tool/grep.test.ts | tool/grep.ts | EXISTS |
| tool/question.test.ts | tool/question.ts | EXISTS |
| tool/read.test.ts | tool/read.ts | EXISTS |
| tool/registry.test.ts | tool/registry.ts | EXISTS |
| tool/truncation.test.ts | tool/truncation.ts | EXISTS |
| util/filesystem.test.ts | util/filesystem.ts | EXISTS |
| util/format.test.ts | util/format.ts | EXISTS |
| util/iife.test.ts | util/iife.ts | EXISTS |
| util/lazy.test.ts | util/lazy.ts | EXISTS |
| util/lock.test.ts | util/lock.ts | EXISTS |
| util/timeout.test.ts | util/timeout.ts | EXISTS |
| util/wildcard.test.ts | util/wildcard.ts | EXISTS |

### 10.2 Untested Modules (needs new tests)

| Module | Priority | Test Scenarios |
|---|---|---|
| acp/types.ts | MEDIUM | Type validation, codec roundtrip |
| api/voice.ts | LOW | Voice API calls, error handling |
| auth/index.ts | HIGH | Token validation, refresh, provider auth |
| bus/bus-event.ts | HIGH | Event construction, serialization |
| bus/global.ts | HIGH | Pub/sub, unsubscribe, concurrency |
| bus/index.ts | LOW | Re-exports |
| cli/bootstrap.ts | HIGH | Init subsystems, config defaults |
| cli/cmd/acp.ts | MEDIUM | Arg parsing, session start |
| cli/cmd/agent.ts | MEDIUM | Agent lifecycle |
| cli/cmd/auth.ts | HIGH | Login/logout flow |
| cli/cmd/cmd.ts | MEDIUM | Command routing |
| cli/cmd/export.ts | LOW | Export formats |
| cli/cmd/generate.ts | LOW | Template generation |
| cli/cmd/import.ts | LOW | Import validation |
| cli/cmd/mcp.ts | HIGH | MCP server, tool listing |
| cli/cmd/models.ts | MEDIUM | Model enumeration |
| cli/cmd/pr.ts | MEDIUM | PR integration |
| cli/cmd/run.ts | HIGH | Non-interactive execution |
| cli/cmd/serve.ts | HIGH | Server startup |
| cli/cmd/session.ts | HIGH | Session management |
| cli/cmd/stats.ts | LOW | Usage statistics |
| cli/cmd/tui/attach.ts | MEDIUM | TUI attachment |
| cli/cmd/tui/event.ts | MEDIUM | Event handling |
| cli/cmd/tui/thread.ts | MEDIUM | Thread rendering |
| cli/cmd/tui/worker.ts | MEDIUM | Background work |
| cli/cmd/tui/component/textarea-keybindings.ts | LOW | Key bindings |
| cli/cmd/tui/context/directory.ts | LOW | Directory context |
| cli/cmd/tui/ui/spinner.ts | LOW | Spinner animation |
| cli/cmd/tui/util/clipboard.ts | LOW | Clipboard ops |
| cli/cmd/tui/util/editor.ts | LOW | Editor launch |
| cli/cmd/tui/util/signal.ts | LOW | Signal handling |
| cli/cmd/tui/util/terminal.ts | LOW | Terminal detection |
| cli/cmd/uninstall.ts | LOW | Uninstall flow |
| cli/cmd/upgrade.ts | MEDIUM | Upgrade flow |
| cli/cmd/web.ts | LOW | Web command |
| cli/cmd/debug/*.ts (8 files) | LOW | Debug subcommands |
| cli/error.ts | MEDIUM | Error formatting |
| cli/logo.ts | LOW | Logo rendering |
| cli/network.ts | MEDIUM | Connectivity check |
| cli/ui.ts | LOW | UI helpers |
| cli/upgrade.ts | MEDIUM | Upgrade check |
| command/index.ts | MEDIUM | Command registry |
| env/index.ts | MEDIUM | Environment reading |
| file/ripgrep.ts | HIGH | Search execution |
| file/time.ts | LOW | File timestamps |
| file/watcher.ts | MEDIUM | File watching |
| flag/flag.ts | MEDIUM | Feature flags |
| format/formatter.ts | MEDIUM | Output formatting |
| format/index.ts | LOW | Re-exports |
| global/index.ts | MEDIUM | Global state |
| id/id.ts | HIGH | ID generation |
| installation/index.ts | MEDIUM | Installation detection |
| lsp/index.ts | LOW | Re-exports |
| lsp/language.ts | MEDIUM | Language detection |
| lsp/server.ts | HIGH | LSP server management |
| mcp/auth.ts | HIGH | MCP OAuth |
| mcp/oauth-provider.ts | MEDIUM | OAuth provider |
| plugin/copilot.ts | MEDIUM | Copilot integration |
| plugin/index.ts | MEDIUM | Plugin registry |
| project/bootstrap.ts | HIGH | Project detection |
| project/instance.ts | HIGH | Instance management |
| project/state.ts | MEDIUM | State persistence |
| project/vcs.ts | MEDIUM | VCS integration |
| provider/auth.ts | HIGH | API key handling |
| provider/models.ts | HIGH | Model catalog |
| provider/sdk/**/*.ts (16 files) | HIGH | SDK implementation |
| pty/index.ts | MEDIUM | PTY management |
| server/error.ts | MEDIUM | Error responses |
| server/event.ts | MEDIUM | SSE events |
| server/mdns.ts | LOW | mDNS |
| server/server.ts | HIGH | Server core |
| server/routes/*.ts (12 files) | MEDIUM-HIGH | Route handlers |
| session/message.ts | HIGH | Message types |
| session/processor.ts | HIGH | Message processing |
| session/prompt.ts | MEDIUM | Prompt templates |
| session/status.ts | MEDIUM | Status tracking |
| session/summary.ts | MEDIUM | Summary generation |
| session/system.ts | HIGH | System prompt |
| session/todo.ts | LOW | Todo tracking |
| share/*.ts (2 files) | MEDIUM | Session sharing |
| shell/shell.ts | HIGH | Shell execution |
| skill/skill.ts | MEDIUM | Skill parsing |
| storage/storage.ts | HIGH | Storage layer |
| tool/batch.ts | MEDIUM | Batch execution |
| tool/codesearch.ts | MEDIUM | Code search |
| tool/edit.ts | HIGH | File editing |
| tool/glob.ts | MEDIUM | Glob patterns |
| tool/invalid.ts | LOW | Invalid tool |
| tool/ls.ts | MEDIUM | Directory listing |
| tool/lsp.ts | MEDIUM | LSP tool |
| tool/multiedit.ts | HIGH | Multi-edit |
| tool/plan.ts | LOW | Plan tool |
| tool/skill.ts | LOW | Skill tool |
| tool/task.ts | MEDIUM | Task tool |
| tool/todo.ts | LOW | Todo tool |
| tool/tool.ts | HIGH | Tool types |
| tool/webfetch.ts | MEDIUM | Web fetch |
| tool/websearch.ts | MEDIUM | Web search |
| tool/write.ts | HIGH | File write |
| util/archive.ts | LOW | Archive utils |
| util/color.ts | LOW | Color utils |
| util/context.ts | MEDIUM | Context utils |
| util/defer.ts | LOW | Defer utils |
| util/eventloop.ts | LOW | Event loop |
| util/fn.ts | LOW | Function utils |
| util/locale.ts | LOW | Locale utils |
| util/log.ts | LOW | Logging |
| util/queue.ts | MEDIUM | Queue impl |
| util/rpc.ts | MEDIUM | RPC utils |
| util/scrap.ts | LOW | Scratch pad |
| util/signal.ts | LOW | Signal utils |
| util/token.ts | HIGH | Token counting |
| worktree/index.ts | MEDIUM | Worktree mgmt |

---


## 11. Cross-Package Integration Tests

### 11.1 forge-core <-> forge/server (WebSocket session lifecycle)

- **Test**: Client connects via WebSocket; creates session; sends message; receives streaming response; session persisted to storage
- **Modules**: Forge.Server.Server, Bridge.WebSocket.Manager, Forge.Session.LLM, Bridge.Database
- **Priority**: HIGH
- **Type**: Integration (spago test + cabal test coordinated)

### 11.2 app <-> forge/server (UI state sync)

- **Test**: App opens; connects to server; session list synced; session state updates propagated in real-time; offline handling
- **Modules**: App.Context.Bridge, Bridge.State.Store, Bridge.WebSocket.Handlers
- **Priority**: HIGH
- **Type**: Integration

### 11.3 Full conversation E2E (prompt -> LLM -> tool -> response)

- **Test**: User sends prompt; LLM returns tool call; tool executed (bash/edit/read); result returned to LLM; final response displayed
- **Modules**: Forge.Session.Processor, Forge.Tool.Registry, Forge.Tool.Bash, Forge.Session.LLM
- **Priority**: HIGH
- **Type**: E2E (requires mock LLM provider)

### 11.4 Multi-provider failover

- **Test**: Primary provider returns 500; system falls back to secondary; request succeeds; usage tracked correctly
- **Modules**: Forge.Provider.Provider, Forge.Session.Retry, Forge.Util.Token
- **Priority**: HIGH
- **Type**: Integration

### 11.5 Session persistence roundtrip

- **Test**: Create session; add messages; save; restart server; load session; verify messages identical
- **Modules**: Forge.Session.Session, Forge.Storage.Storage, Bridge.Database
- **Priority**: HIGH
- **Type**: Integration
- **Property**: prop_sessionPersistenceRoundtrip

### 11.6 Permission lifecycle E2E

- **Test**: Tool requires permission; user approves; tool executes; permission cached; subsequent calls auto-approved
- **Modules**: Forge.Permission.Index, Forge.Permission.Next, Forge.Tool.Bash
- **Priority**: HIGH
- **Type**: E2E

### 11.7 Compaction and revert interaction

- **Test**: Session hits compaction threshold; compaction runs; user reverts; compacted content correctly handled
- **Modules**: Forge.Session.Compaction, Forge.Session.Revert, Forge.Session.Message
- **Priority**: HIGH
- **Type**: Integration
- **Property**: prop_revertAfterCompactionConsistent

### 11.8 Console omega -> LLM provider roundtrip

- **Test**: API request to omega endpoint; routed to correct provider; response streamed back; usage metered; billing updated
- **Modules**: Console.Omega.Handler.Main, Console.Omega.Provider.*, Render.Billing.NVXT
- **Priority**: HIGH
- **Type**: E2E

---

## 12. Property Test Catalog

### 12.1 Codec Properties (JSON roundtrip for every serializable type)

| Property | Types Covered | Package |
|---|---|---|
| prop_messageCodecRoundtrip | Message, MessageV2, MessagePart | forge-core |
| prop_sessionCodecRoundtrip | Session, SessionStatus, SessionConfig | forge-core |
| prop_toolCodecRoundtrip | ToolCall, ToolResult, ToolDefinition | forge-core |
| prop_providerCodecRoundtrip | ProviderConfig, ModelInfo, AuthToken | forge-core |
| prop_configCodecRoundtrip | Config, ProjectConfig, GlobalConfig | forge-core |
| prop_eventCodecRoundtrip | BusEvent, SSEEvent, WebSocketMessage | forge-core |
| prop_enterpriseTypeCodecRoundtrip | BillingRecord, AuditEntry, ShareLink | enterprise |
| prop_schemaCodecRoundtrip | Account, Workspace, Key, User | console |
| prop_apiTypeCodecRoundtrip | OpenAI request/response types | forge-core/sdk |
| prop_forgeTypesCodecRoundtrip | All Forge.Types.* | forge/types |

### 12.2 State Machine Properties

| Property | Description | Package |
|---|---|---|
| prop_sessionStatusTransitionValid | No backward transitions from terminal states | forge-core |
| prop_storeReducerCommutative | Commutative reducers produce same state | forge/server |
| prop_circuitBreakerStateValid | Only valid state transitions (closed->open->half-open) | enterprise |
| prop_permissionLatticePreserved | Permission ordering maintained after transitions | forge-core |
| prop_balanceNonNegative | Balance never goes below zero | app |
| prop_rateLimiterTokenBounded | Tokens never exceed burst capacity | enterprise, console |

### 12.3 Idempotency Properties

| Property | Description | Package |
|---|---|---|
| prop_editIdempotent | apply(apply(edit, file), file) = apply(edit, file) | forge-core |
| prop_configMergeIdempotent | merge(cfg, cfg) = cfg | forge-core |
| prop_validationIdempotent | validate(validate(x)) = validate(x) | forge-core |
| prop_normalizeIdempotent | normalize(normalize(path)) = normalize(path) | forge-core |
| prop_slugIdempotent | slug(slug(s)) = slug(s) | forge-core |
| prop_ignorePatternIdempotent | matches twice = matches once | forge-core |

### 12.4 Monotonicity Properties

| Property | Description | Package |
|---|---|---|
| prop_tokenUsageMonotonic | Token count only increases during session | forge-core |
| prop_costAccumulationMonotonic | Total cost never decreases | forge-core |
| prop_backoffMonotonic | Retry delay increases on each attempt | forge-core |
| prop_transcriptLengthMonotonic | Transcript only grows | forge-core |
| prop_clockMonotonic | Clock readings never decrease | enterprise |
| prop_auditTrailAppendOnly | Audit entries only added, never removed | enterprise |
| prop_upgradeVersionMonotonic | Version number only increases | forge-core |
| prop_countdownMonotonic | Countdown timer only decreases | app |

### 12.5 Commutativity Properties

| Property | Description | Package |
|---|---|---|
| prop_configMergeAssociative | merge(a, merge(b, c)) = merge(merge(a, b), c) | forge-core |
| prop_composeAssociative | f . (g . h) = (f . g) . h | forge-core |
| prop_storeReducerCommutative | For independent actions: reduce(a, reduce(b, s)) = reduce(b, reduce(a, s)) | forge/server |

### 12.6 Bounds Properties

| Property | Description | Package |
|---|---|---|
| prop_exitCodeBounded | Exit codes in [0, 255] | forge-core |
| prop_errorStatusCodeBounded | HTTP status in [400, 599] | forge-core |
| prop_serverPortBounded | Port in [1024, 65535] | forge-core |
| prop_temperatureBounded | Temperature in [0, 2] | forge-core/sdk |
| prop_topPBounded | top_p in [0, 1] | forge-core/sdk |
| prop_progressBarBounded | Progress in [0, 100] | forge-core |
| prop_tokenCountNonNegative | Token count >= 0 | forge-core |
| prop_modelContextWindowPositive | Context window > 0 | forge-core |
| prop_queueBounded | Queue size <= max capacity | enterprise |

---


## 13. Appendix: Module-to-Test Mapping Table

Complete listing of every module with test status.

Format: Package | Module | File Path | Has Test? | Test Priority | Test Types Needed

### 13.1 forge-core (204 modules)

| Package | Module | File Path | Has Test? | Priority | Types Needed |
|---|---|---|---|---|---|
| forge-core | ACP.Agent | src/acp/Agent.purs | No | HIGH | Unit, Property |
| forge-core | ACP.Session | src/acp/Session.purs | No | HIGH | Unit, Property |
| forge-core | ACP.Types | src/acp/Types.purs | No | MEDIUM | Property |
| forge-core | Agent.Agent | src/agent/Agent.purs | No | HIGH | Unit, Property |
| forge-core | Auth.Index | src/auth/Index.purs | No | HIGH | Unit, Property |
| forge-core | Bridge.FFI.Node.Process | src/bridge/FFI/Node/Process.purs | No | MEDIUM | Unit |
| forge-core | Bridge.Utils.Validation | src/bridge/Utils/Validation.purs | No | HIGH | Unit, Property |
| forge-core | Bun.Index | src/bun/Index.purs | No | LOW | Unit |
| forge-core | Bus.BusEvent | src/bus/BusEvent.purs | No | HIGH | Unit, Property |
| forge-core | Bus.Global | src/bus/Global.purs | No | HIGH | Unit, Property |
| forge-core | Bus.Index | src/bus/Index.purs | No | MEDIUM | Unit |
| forge-core | CLI.Bootstrap | src/cli/Bootstrap.purs | No | HIGH | Unit, Property |
| forge-core | CLI.Error | src/cli/Error.purs | No | MEDIUM | Unit, Property |
| forge-core | CLI.Logo | src/cli/Logo.purs | No | LOW | Unit |
| forge-core | CLI.Network | src/cli/Network.purs | No | MEDIUM | Unit |
| forge-core | CLI.UI | src/cli/UI.purs | No | LOW | Unit |
| forge-core | CLI.Upgrade | src/cli/Upgrade.purs | No | MEDIUM | Unit, Property |
| forge-core | CLI.Cmd.Acp | src/cli/cmd/Acp.purs | No | MEDIUM | Unit |
| forge-core | CLI.Cmd.Agent | src/cli/cmd/Agent.purs | No | MEDIUM | Unit |
| forge-core | CLI.Cmd.Auth | src/cli/cmd/Auth.purs | No | HIGH | Unit |
| forge-core | CLI.Cmd.Cmd | src/cli/cmd/Cmd.purs | No | MEDIUM | Unit |
| forge-core | CLI.Cmd.Export | src/cli/cmd/Export.purs | No | LOW | Unit, Property |
| forge-core | CLI.Cmd.Generate | src/cli/cmd/Generate.purs | No | LOW | Unit |
| forge-core | CLI.Cmd.Github | src/cli/cmd/Github.purs | No | MEDIUM | Unit |
| forge-core | CLI.Cmd.Import | src/cli/cmd/Import.purs | No | LOW | Unit, Property |
| forge-core | CLI.Cmd.Mcp | src/cli/cmd/Mcp.purs | No | HIGH | Unit |
| forge-core | CLI.Cmd.Models | src/cli/cmd/Models.purs | No | MEDIUM | Unit |
| forge-core | CLI.Cmd.Pr | src/cli/cmd/Pr.purs | No | MEDIUM | Unit |
| forge-core | CLI.Cmd.Run | src/cli/cmd/Run.purs | No | HIGH | Unit, Property |
| forge-core | CLI.Cmd.Serve | src/cli/cmd/Serve.purs | No | HIGH | Unit |
| forge-core | CLI.Cmd.Session | src/cli/cmd/Session.purs | No | HIGH | Unit |
| forge-core | CLI.Cmd.Stats | src/cli/cmd/Stats.purs | No | LOW | Unit, Property |
| forge-core | CLI.Cmd.Uninstall | src/cli/cmd/Uninstall.purs | No | LOW | Unit |
| forge-core | CLI.Cmd.Upgrade | src/cli/cmd/Upgrade.purs | No | MEDIUM | Unit, Property |
| forge-core | CLI.Cmd.Web | src/cli/cmd/Web.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Agent | src/cli/cmd/debug/Agent.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Config | src/cli/cmd/debug/Config.purs | No | LOW | Unit |
| forge-core | CLI.Debug.File | src/cli/cmd/debug/File.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Index | src/cli/cmd/debug/Index.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Lsp | src/cli/cmd/debug/Lsp.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Ripgrep | src/cli/cmd/debug/Ripgrep.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Scrap | src/cli/cmd/debug/Scrap.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Skill | src/cli/cmd/debug/Skill.purs | No | LOW | Unit |
| forge-core | CLI.Debug.Snapshot | src/cli/cmd/debug/Snapshot.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Attach | src/cli/cmd/tui/Attach.purs | No | MEDIUM | Unit |
| forge-core | CLI.TUI.Event | src/cli/cmd/tui/Event.purs | No | MEDIUM | Unit, Property |
| forge-core | CLI.TUI.Thread | src/cli/cmd/tui/Thread.purs | No | MEDIUM | Unit, Property |
| forge-core | CLI.TUI.Worker | src/cli/cmd/tui/Worker.purs | No | MEDIUM | Unit, Property |
| forge-core | CLI.TUI.TextareaKeybindings | src/cli/cmd/tui/component/TextareaKeybindings.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Directory | src/cli/cmd/tui/context/Directory.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Spinner | src/cli/cmd/tui/ui/Spinner.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Clipboard | src/cli/cmd/tui/util/Clipboard.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Editor | src/cli/cmd/tui/util/Editor.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Signal | src/cli/cmd/tui/util/Signal.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Terminal | src/cli/cmd/tui/util/Terminal.purs | No | LOW | Unit |
| forge-core | CLI.TUI.Transcript | src/cli/cmd/tui/util/Transcript.purs | No | LOW | Unit, Property |
| forge-core | Command.Index | src/command/Index.purs | No | MEDIUM | Unit |
| forge-core | Config.Config | src/config/Config.purs | No | HIGH | Unit, Property |
| forge-core | Config.Markdown | src/config/Markdown.purs | No | MEDIUM | Unit, Property |
| forge-core | Env.Index | src/env/Index.purs | No | MEDIUM | Unit |
| forge-core | File.File | src/file/File.purs | No | HIGH | Unit, Property |
| forge-core | File.Ignore | src/file/Ignore.purs | No | HIGH | Unit, Property |
| forge-core | File.Index | src/file/Index.purs | No | MEDIUM | Unit |
| forge-core | File.Ripgrep | src/file/Ripgrep.purs | No | HIGH | Unit, Property |
| forge-core | File.Time | src/file/Time.purs | No | LOW | Unit |
| forge-core | File.Watcher | src/file/Watcher.purs | No | MEDIUM | Unit |
| forge-core | Flag.Flag | src/flag/Flag.purs | No | MEDIUM | Unit |
| forge-core | Format.Formatter | src/format/Formatter.purs | No | MEDIUM | Unit |
| forge-core | Format.Index | src/format/Index.purs | No | LOW | Unit |
| forge-core | Global.Index | src/global/Index.purs | No | MEDIUM | Unit |
| forge-core | Id.Id | src/id/Id.purs | No | HIGH | Unit, Property |
| forge-core | IDE.Index | src/ide/Index.purs | No | MEDIUM | Unit |
| forge-core | Installation.Index | src/installation/Index.purs | No | MEDIUM | Unit |
| forge-core | LSP.Client | src/lsp/Client.purs | No | HIGH | Unit, Property |
| forge-core | LSP.Index | src/lsp/Index.purs | No | LOW | Unit |
| forge-core | LSP.Language | src/lsp/Language.purs | No | MEDIUM | Unit |
| forge-core | LSP.Server | src/lsp/Server.purs | No | HIGH | Unit |
| forge-core | MCP.Auth | src/mcp/Auth.purs | No | HIGH | Unit, Property |
| forge-core | MCP.Index | src/mcp/Index.purs | No | HIGH | Unit, Property |
| forge-core | MCP.OAuthCallback | src/mcp/OAuthCallback.purs | No | MEDIUM | Unit |
| forge-core | MCP.OAuthProvider | src/mcp/OAuthProvider.purs | No | MEDIUM | Unit |
| forge-core | Patch.Index | src/patch/Index.purs | No | HIGH | Unit, Property |
| forge-core | Permission.Arity | src/permission/Arity.purs | No | HIGH | Unit, Property |
| forge-core | Permission.Index | src/permission/Index.purs | No | HIGH | Unit, Property |
| forge-core | Permission.Next | src/permission/Next.purs | No | HIGH | Unit, Property |
| forge-core | Plugin.Codex | src/plugin/Codex.purs | No | MEDIUM | Unit |
| forge-core | Plugin.Copilot | src/plugin/Copilot.purs | No | MEDIUM | Unit |
| forge-core | Plugin.Index | src/plugin/Index.purs | No | MEDIUM | Unit |
| forge-core | Project.Bootstrap | src/project/Bootstrap.purs | No | HIGH | Unit |
| forge-core | Project.Instance | src/project/Instance.purs | No | HIGH | Unit, Property |
| forge-core | Project.Project | src/project/Project.purs | No | HIGH | Unit |
| forge-core | Project.State | src/project/State.purs | No | MEDIUM | Unit, Property |
| forge-core | Project.VCS | src/project/VCS.purs | No | MEDIUM | Unit |
| forge-core | Provider.Auth | src/provider/Auth.purs | No | HIGH | Unit |
| forge-core | Provider.Models | src/provider/Models.purs | No | HIGH | Unit, Property |
| forge-core | Provider.Provider | src/provider/Provider.purs | No | HIGH | Unit, Property |
| forge-core | Provider.Transform | src/provider/Transform.purs | No | HIGH | Unit, Property |
| forge-core | Provider.SDK.OAI.Index | src/provider/sdk/openai-compatible/Index.purs | No | HIGH | Unit |
| forge-core | Provider.SDK.OAI.Provider | src/provider/sdk/openai-compatible/Provider.purs | No | HIGH | Unit, Property |
| forge-core | Provider.SDK.ConvertInput | src/provider/sdk/.../ConvertToOpenAIResponsesInput.purs | No | HIGH | Unit, Property |
| forge-core | Provider.SDK.MapFinishReason | src/provider/sdk/.../MapOpenAIResponsesFinishReason.purs | No | MEDIUM | Unit |
| forge-core | Provider.SDK.Config | src/provider/sdk/.../OpenAIConfig.purs | No | MEDIUM | Unit |
| forge-core | Provider.SDK.Error | src/provider/sdk/.../OpenAIError.purs | No | MEDIUM | Unit, Property |
| forge-core | Provider.SDK.APITypes | src/provider/sdk/.../OpenAIResponsesAPITypes.purs | No | MEDIUM | Property |
| forge-core | Provider.SDK.LanguageModel | src/provider/sdk/.../OpenAIResponsesLanguageModel.purs | No | HIGH | Unit, Property |
| forge-core | Provider.SDK.PrepareTools | src/provider/sdk/.../OpenAIResponsesPrepareTools.purs | No | MEDIUM | Unit |
| forge-core | Provider.SDK.Settings | src/provider/sdk/.../OpenAIResponsesSettings.purs | No | MEDIUM | Unit, Property |
| forge-core | Provider.SDK.Tool.* (6) | src/provider/sdk/.../tool/*.purs | No | LOW | Unit |
| forge-core | PTY.Index | src/pty/Index.purs | No | MEDIUM | Unit |
| forge-core | Question.Index | src/question/Index.purs | No | MEDIUM | Unit |
| forge-core | Scheduler.Index | src/scheduler/Index.purs | No | MEDIUM | Unit, Property |
| forge-core | Server.Error | src/server/Error.purs | No | MEDIUM | Unit, Property |
| forge-core | Server.Event | src/server/Event.purs | No | MEDIUM | Unit |
| forge-core | Server.MDNS | src/server/MDNS.purs | No | LOW | Unit |
| forge-core | Server.Server | src/server/Server.purs | No | HIGH | Unit |
| forge-core | Server.Routes.* (12) | src/server/routes/*.purs | No | MEDIUM-HIGH | Unit |
| forge-core | Session.Compaction | src/session/Compaction.purs | No | HIGH | Unit, Property |
| forge-core | Session.Index | src/session/Index.purs | No | HIGH | Unit, Property |
| forge-core | Session.Instruction | src/session/Instruction.purs | No | HIGH | Unit, Property |
| forge-core | Session.LLM | src/session/LLM.purs | No | HIGH | Unit, Property |
| forge-core | Session.LLMTypes | src/session/LLMTypes.purs | No | MEDIUM | Property |
| forge-core | Session.Message | src/session/Message.purs | No | HIGH | Unit, Property |
| forge-core | Session.MessageV2 | src/session/MessageV2.purs | No | HIGH | Unit, Property |
| forge-core | Session.Processor | src/session/Processor.purs | No | HIGH | Unit, Property |
| forge-core | Session.Prompt | src/session/Prompt.purs | No | MEDIUM | Unit |
| forge-core | Session.Retry | src/session/Retry.purs | No | HIGH | Unit, Property |
| forge-core | Session.Revert | src/session/Revert.purs | No | HIGH | Unit, Property |
| forge-core | Session.Session | src/session/Session.purs | No | HIGH | Unit, Property |
| forge-core | Session.Status | src/session/Status.purs | No | MEDIUM | Unit, Property |
| forge-core | Session.Summary | src/session/Summary.purs | No | MEDIUM | Unit |
| forge-core | Session.System | src/session/System.purs | No | HIGH | Unit |
| forge-core | Session.Todo | src/session/Todo.purs | No | LOW | Unit |
| forge-core | Share.Share | src/share/Share.purs | No | MEDIUM | Unit |
| forge-core | Share.ShareNext | src/share/ShareNext.purs | No | MEDIUM | Unit, Property |
| forge-core | Shell.Shell | src/shell/Shell.purs | No | HIGH | Unit, Property |
| forge-core | Skill.Index | src/skill/Index.purs | No | MEDIUM | Unit |
| forge-core | Skill.Skill | src/skill/Skill.purs | No | MEDIUM | Unit, Property |
| forge-core | Snapshot.Index | src/snapshot/Index.purs | No | HIGH | Unit, Property |
| forge-core | Storage.Storage | src/storage/Storage.purs | No | HIGH | Unit, Property |
| forge-core | Tool.* (24 modules) | src/tool/*.purs | No | HIGH | Unit, Property |
| forge-core | Util.* (22 modules) | src/util/*.purs | No | LOW-HIGH | Unit, Property |
| forge-core | Worktree.Index | src/worktree/Index.purs | No | MEDIUM | Unit |
| forge-core | Index | src/Index.purs | No | LOW | Unit |


### 13.2 app (70 modules)

| Package | Module | Has Test? | Priority | Types Needed |
|---|---|---|---|---|
| app | App | No | HIGH | Unit |
| app | AppM | No | HIGH | Unit |
| app | Voice.AudioVisualizer | No | LOW | Unit |
| app | Voice.MicrophoneButton | No | LOW | Unit |
| app | Voice.TranscriptView | No | LOW | Unit |
| app | Voice.VoiceSelector | No | LOW | Unit |
| app | Addons.Serialize | Yes (Spec) | HIGH | Property |
| app | Components.AlertSystem | No | MEDIUM | Unit |
| app | Components.Balance.BalanceTracker | No | HIGH | Unit, Property |
| app | Components.Balance.CountdownTimer | No | MEDIUM | Unit, Property |
| app | Components.Balance.DiemTracker | No | MEDIUM | Unit |
| app | Components.CodeSelection | No | MEDIUM | Unit |
| app | Components.CommandPalette | No | MEDIUM | Unit |
| app | Components.Dashboard | No | MEDIUM | Unit |
| app | Components.DiffViewer | No | HIGH | Unit |
| app | Components.FileContextView | No | MEDIUM | Unit |
| app | Components.HelpOverlay | No | LOW | Unit |
| app | Components.KeyboardNavigation | No | MEDIUM | Unit |
| app | Components.Proof.ProofPanel | No | LOW | Unit |
| app | Components.Settings.SettingsPanel | No | MEDIUM | Unit |
| app | Components.Sidebar | No | MEDIUM | Unit |
| app | Components.TerminalEmbed | No | MEDIUM | Unit |
| app | Components.TokenUsageChart | No | MEDIUM | Unit |
| app | Components.Session.SessionPanel | No | HIGH | Unit |
| app | Context.Bridge | Yes (BridgeSpec) | HIGH | Unit |
| app | Context.Command | No | MEDIUM | Unit |
| app | Context.Comments | No | LOW | Unit |
| app | Context.File | No | MEDIUM | Unit |
| app | Context.GlobalSDK | No | MEDIUM | Unit |
| app | Context.GlobalSync | No | MEDIUM | Unit |
| app | Context.Highlights | No | MEDIUM | Unit |
| app | Context.Language | No | MEDIUM | Unit |
| app | Context.Layout | No | MEDIUM | Unit |
| app | Context.LayoutScroll | No | MEDIUM | Unit |
| app | Context.Local | No | MEDIUM | Unit |
| app | Context.Models | No | MEDIUM | Unit |
| app | Context.Notification | No | MEDIUM | Unit |
| app | Context.Permission | No | MEDIUM | Unit |
| app | Context.Platform | No | MEDIUM | Unit |
| app | Context.Prompt | No | MEDIUM | Unit |
| app | Context.SDK | No | MEDIUM | Unit |
| app | Context.Server | No | MEDIUM | Unit |
| app | Context.Settings | No | MEDIUM | Unit |
| app | Context.Sync | No | MEDIUM | Unit |
| app | Context.Terminal | No | MEDIUM | Unit |
| app | Context.Types | No | MEDIUM | Property |
| app | Hooks.UseProviders | No | MEDIUM | Unit |
| app | Hooks.UseVoice | No | LOW | Unit |
| app | I18n.En | No | LOW | Unit |
| app | I18n.I18n | No | LOW | Unit |
| app | I18n.Types | No | LOW | Property |
| app | Pages.DirectoryLayout | No | MEDIUM | Unit |
| app | Pages.Error | No | MEDIUM | Unit |
| app | Pages.Home | No | MEDIUM | Unit |
| app | Pages.Layout | No | MEDIUM | Unit |
| app | Pages.Session | No | MEDIUM | Unit |
| app | Pages.Voice | No | LOW | Unit |
| app | Utils.Agent | No | MEDIUM | Unit |
| app | Utils.Base64 | No | MEDIUM | Unit, Property |
| app | Utils.Dom | No | MEDIUM | Unit |
| app | Utils.Id | No | HIGH | Unit, Property |
| app | Utils.Maybe | No | MEDIUM | Unit |
| app | Utils.Perf | No | LOW | Unit |
| app | Utils.Persist | No | MEDIUM | Unit |
| app | Utils.Prompt | No | MEDIUM | Unit |
| app | Utils.Same | No | LOW | Unit |
| app | Utils.SolidDnd | No | LOW | Unit |
| app | Utils.Sound | No | LOW | Unit |
| app | Utils.Speech | No | LOW | Unit |
| app | Utils.Worktree | No | MEDIUM | Unit |

### 13.3 ui (88 modules)

| Package | Module | Has Test? | Priority | Types Needed |
|---|---|---|---|---|
| ui | Components.Accordion | No | MEDIUM | Unit |
| ui | Components.Avatar | No | LOW | Unit |
| ui | Components.BasicTool | No | MEDIUM | Unit |
| ui | Components.Button | No | HIGH | Unit |
| ui | Components.Card | No | LOW | Unit |
| ui | Components.Checkbox | No | MEDIUM | Unit |
| ui | Components.Code | No | MEDIUM | Unit |
| ui | Components.Collapsible | No | MEDIUM | Unit |
| ui | Components.Dialog | No | MEDIUM | Unit |
| ui | Components.Diff | No | HIGH | Unit |
| ui | Components.DiffChanges | No | HIGH | Unit |
| ui | Components.DiffSsr | No | MEDIUM | Unit |
| ui | Components.DropdownMenu | No | MEDIUM | Unit |
| ui | Components.Favicon | No | LOW | Unit |
| ui | Components.FileIcon | No | LOW | Unit |
| ui | Components.Font | No | LOW | Unit |
| ui | Components.HoverCard | No | LOW | Unit |
| ui | Components.Icon | No | LOW | Unit |
| ui | Components.IconButton | No | LOW | Unit |
| ui | Components.ImagePreview | No | LOW | Unit |
| ui | Components.InlineInput | No | MEDIUM | Unit |
| ui | Components.Keybind | No | MEDIUM | Unit |
| ui | Components.LineComment | No | MEDIUM | Unit |
| ui | Components.List | No | MEDIUM | Unit |
| ui | Components.Logo | No | LOW | Unit |
| ui | Components.Markdown | No | HIGH | Unit |
| ui | Components.MessageNav | No | HIGH | Unit |
| ui | Components.MessagePart | No | HIGH | Unit |
| ui | Components.MessagePart.Component | No | HIGH | Unit |
| ui | Components.MessagePart.Registry | No | HIGH | Unit |
| ui | Components.MessagePart.Types | No | MEDIUM | Property |
| ui | Components.Popover | No | LOW | Unit |
| ui | Components.ProgressCircle | No | LOW | Unit |
| ui | Components.ProviderIcon | No | LOW | Unit |
| ui | Components.RadioGroup | No | MEDIUM | Unit |
| ui | Components.ResizeHandle | No | MEDIUM | Unit |
| ui | Components.Select | No | MEDIUM | Unit |
| ui | Components.SessionReview | No | HIGH | Unit |
| ui | Components.SessionTurn | No | HIGH | Unit |
| ui | Components.SessionTurn.Component | No | HIGH | Unit |
| ui | Components.SessionTurn.Status | No | MEDIUM | Unit |
| ui | Components.SessionTurn.Types | No | MEDIUM | Property |
| ui | Components.Spinner | No | LOW | Unit |
| ui | Components.StickyAccordionHeader | No | LOW | Unit |
| ui | Components.Switch | No | MEDIUM | Unit |
| ui | Components.Tabs | No | MEDIUM | Unit |
| ui | Components.Tag | No | LOW | Unit |
| ui | Components.TextField | No | MEDIUM | Unit |
| ui | Components.Toast | No | MEDIUM | Unit |
| ui | Components.Tooltip | No | LOW | Unit |
| ui | Components.Typewriter | No | LOW | Unit |
| ui | Context.Code | No | MEDIUM | Unit |
| ui | Context.Data | No | MEDIUM | Unit |
| ui | Context.Dialog | No | MEDIUM | Unit |
| ui | Context.Diff | No | MEDIUM | Unit |
| ui | Context.Helper | No | MEDIUM | Unit |
| ui | Context.I18n | No | MEDIUM | Unit |
| ui | Context.Index | No | LOW | Unit |
| ui | Context.Marked | No | MEDIUM | Unit |
| ui | Context.WorkerPool | No | MEDIUM | Unit |
| ui | Hooks.CreateAutoScroll | No | MEDIUM | Unit |
| ui | Hooks.Index | No | LOW | Unit |
| ui | Hooks.UseFilteredList | No | MEDIUM | Unit, Property |
| ui | I18n.* (16 locales) | No | LOW | Unit, Property |
| ui | Pierre.Index | No | MEDIUM | Unit |
| ui | Pierre.Types | No | MEDIUM | Property |
| ui | Pierre.Worker | No | MEDIUM | Unit |
| ui | Theme.Color | No | MEDIUM | Unit |
| ui | Theme.Context | No | MEDIUM | Unit |
| ui | Theme.Contrast | No | MEDIUM | Unit, Property |
| ui | Theme.Index | No | LOW | Unit |
| ui | Theme.Loader | No | MEDIUM | Unit |
| ui | Theme.Palette | No | MEDIUM | Unit |
| ui | Theme.Resolve | No | MEDIUM | Unit |
| ui | Theme.Types | No | MEDIUM | Property |


### 13.4 forge (76 modules total)

| Package | Module | Has Test? | Priority | Types Needed |
|---|---|---|---|---|
| forge/plugin | Bridge.FFI.Forge.Plugin | Yes | HIGH | Unit |
| forge/plugin | Bridge.FFI.WebSocket.Client | Yes | HIGH | Unit |
| forge/plugin | Forge.Plugin.Main | Yes | HIGH | Unit |
| forge/server | Bridge.Auth.JWT | No | HIGH | Unit, Property |
| forge/server | Bridge.Auth.Origin | No | HIGH | Unit |
| forge/server | Bridge.Auth.RBAC | No | HIGH | Unit, Property |
| forge/server | Bridge.Auth.RateLimit | No | HIGH | Unit, Property |
| forge/server | Bridge.Auth.Session | No | HIGH | Unit |
| forge/server | Bridge.Config | Yes | HIGH | Unit, Property |
| forge/server | Bridge.Database.Sync | No | HIGH | Unit |
| forge/server | Bridge.Error.Retry | No | MEDIUM | Unit, Property |
| forge/server | Bridge.Error.Taxonomy | No | MEDIUM | Unit |
| forge/server | Bridge.FFI.Forge.SDK | No | HIGH | Unit |
| forge/server | Bridge.FFI.Haskell.Analytics | No | HIGH | Unit |
| forge/server | Bridge.FFI.Haskell.Database | No | HIGH | Unit |
| forge/server | Bridge.FFI.Node.Database | Yes | HIGH | Unit |
| forge/server | Bridge.FFI.Node.Express | Yes | HIGH | Unit |
| forge/server | Bridge.FFI.Node.Fetch | Yes | HIGH | Unit |
| forge/server | Bridge.FFI.Node.FileContext | No | MEDIUM | Unit |
| forge/server | Bridge.FFI.Node.Handlers | Yes | HIGH | Unit |
| forge/server | Bridge.FFI.Node.Http | No | MEDIUM | Unit |
| forge/server | Bridge.FFI.Node.Pino | Yes | LOW | Unit |
| forge/server | Bridge.FFI.Node.Process | No | MEDIUM | Unit |
| forge/server | Bridge.FFI.Node.Terminal | No | LOW | Unit |
| forge/server | Bridge.FFI.Node.WebSearch | No | MEDIUM | Unit |
| forge/server | Bridge.FFI.Node.WebSocket | Yes | HIGH | Unit |
| forge/server | Bridge.Forge.Client | No | HIGH | Unit |
| forge/server | Bridge.Forge.Events | No | HIGH | Unit |
| forge/server | Bridge.Lean.Proxy | No | MEDIUM | Unit |
| forge/server | Bridge.Logging.Structured | No | LOW | Unit |
| forge/server | Bridge.Main | Yes | HIGH | Unit |
| forge/server | Bridge.Notifications.Service | Yes | MEDIUM | Unit |
| forge/server | Bridge.Security.Headers | No | HIGH | Unit, Property |
| forge/server | Bridge.Security.Validation | No | HIGH | Unit |
| forge/server | Bridge.Server | Yes | HIGH | Unit |
| forge/server | Bridge.State.Store | Yes | HIGH | Unit, Property |
| forge/server | Bridge.Tracing.OpenTelemetry | No | LOW | Unit |
| forge/server | Bridge.Utils.ErrorHandling | Yes | HIGH | Unit |
| forge/server | Bridge.Utils.Json | Yes | HIGH | Unit, Property |
| forge/server | Bridge.Utils.Metrics | Yes | MEDIUM | Unit |
| forge/server | Bridge.Utils.Time | Yes | MEDIUM | Unit |
| forge/server | Bridge.Utils.Validation | Yes | HIGH | Unit, Property |
| forge/server | Bridge.Venice.Client | No | HIGH | Unit |
| forge/server | Bridge.Venice.RateLimiter | Yes | HIGH | Unit, Property |
| forge/server | Bridge.WebSocket.Handlers | No | HIGH | Unit |
| forge/server | Bridge.WebSocket.Manager | Yes | HIGH | Unit |
| forge/storage | Bridge.Database | Yes | HIGH | Unit, Property |
| forge/storage | Bridge.Database.Operations | Yes | HIGH | Unit |
| forge/storage | Bridge.Database.Schema | Yes | HIGH | Unit |
| forge/storage | Bridge.Alerts.System | No | HIGH | Unit |
| forge/storage | Bridge.Auth.Encryption | No | HIGH | Unit, Property |
| forge/storage | Bridge.Backup.Scheduler | Yes | HIGH | Unit |
| forge/storage | Bridge.Backup.Verification | Yes | HIGH | Unit |
| forge/storage | Bridge.Error.CircuitBreaker | No | HIGH | Unit, Property |
| forge/storage | Bridge.Metrics.Prometheus | No | MEDIUM | Unit |
| forge/storage | Bridge.Performance.Benchmarks | No | MEDIUM | Unit |
| forge/storage | Bridge.Security.Secrets | No | HIGH | Unit |
| forge/analytics | Bridge.Analytics | Yes | HIGH | Unit |
| forge/analytics | Bridge.Analytics.DuckDB | Yes | HIGH | Unit |
| forge/analytics | Bridge.Analytics.Queries | Yes | HIGH | Unit, Property |
| forge/types | Forge.Types (11 modules) | No | HIGH | Property |
| forge/util | Validator.BannedConstructs | Yes | HIGH | Unit |
| forge/util | Validator.FileReading | Yes | HIGH | Unit |
| forge/util | Validator.Main | No | HIGH | Unit |
| forge/util | Validator.TypeEscapes | Yes | HIGH | Unit |

### 13.5 enterprise (18 modules)

| Package | Module | Has Test? | Priority | Types Needed |
|---|---|---|---|---|
| enterprise | Render.Client | No | HIGH | Unit |
| enterprise | Render.Types | No | HIGH | Property |
| enterprise | Render.Billing.NVXT | No | HIGH | Unit, Property |
| enterprise | Render.CAS.Client | No | HIGH | Unit, Property |
| enterprise | Render.ClickHouse.Client | No | HIGH | Unit |
| enterprise | Render.Compliance.AuditTrail | No | HIGH | Unit, Property |
| enterprise | Render.Core.Share | No | HIGH | Unit |
| enterprise | Render.Core.Storage | No | HIGH | Unit, Property |
| enterprise | Render.Gateway.Backend | No | HIGH | Unit, Property |
| enterprise | Render.Gateway.Capacity.Queueing | No | HIGH | Unit, Property |
| enterprise | Render.Gateway.ClickHouse.Schema | No | MEDIUM | Unit |
| enterprise | Render.Gateway.Core | No | HIGH | Unit |
| enterprise | Render.Gateway.STM.CircuitBreaker | No | HIGH | Unit, Property |
| enterprise | Render.Gateway.STM.Clock | No | LOW | Unit, Property |
| enterprise | Render.Gateway.STM.Queue | No | HIGH | Unit, Property |
| enterprise | Render.Gateway.STM.RateLimiter | No | HIGH | Unit, Property |
| enterprise | Render.Gateway.Server | No | HIGH | Unit |
| enterprise | Render.Gateway.Main | No | HIGH | Unit |

### 13.6 console (131 modules)

| Package | Module | Has Test? | Priority |
|---|---|---|---|
| console/core | Account | No | HIGH |
| console/core | Actor | No | HIGH |
| console/core | Context | No | HIGH |
| console/core | Identifier | No | HIGH |
| console/core | Key | No | HIGH |
| console/core | Provider | No | HIGH |
| console/core | Workspace | No | HIGH |
| console/core | Drizzle.Database | No | HIGH |
| console/core | Schema.* (9 modules) | No | HIGH |
| console/core | Util.* (5 modules) | No | MEDIUM |
| console/app | App + core (8 modules) | No | HIGH |
| console/app | Sidepanel.* (3) | Partial (2 specs) | MEDIUM |
| console/app | Component.* (10) | No | MEDIUM |
| console/app | Context.* (3) | No | HIGH |
| console/app | Lib.* (2) | No | MEDIUM |
| console/app | Routes.* (50+) | No | MEDIUM-HIGH |
| console/app | Omega.Handler.* (9) | Partial (2 specs) | HIGH |
| console/app | Omega.Util.* (8) | Partial (many specs) | HIGH |
| console/app | Omega.Provider.* (16) | Yes (14 specs) | HIGH |
| console/app | Omega.V1.* (5) | No | HIGH |
| console/app | Stripe.* (8) | No | HIGH |
| console/app | Workspace.* (15+) | No | HIGH |

---

## 14. Summary Statistics

| Category | Count |
|---|---|
| Total source modules (all packages) | ~670 |
| Total existing test files | 113 |
| Modules with tests | ~120 |
| Modules without tests | ~550 |
| HIGH priority untested modules | ~180 |
| MEDIUM priority untested modules | ~200 |
| LOW priority untested modules | ~170 |
| Required new property tests | ~200 |
| Required new unit test files | ~400 |
| Required new integration tests | ~20 |
| Required new E2E tests | ~8 |

### Priority Order for Test Implementation

1. **Phase 1 (Critical)**: Session, Tool, Provider, Permission, Auth modules across forge-core and opencode
2. **Phase 2 (High)**: Server, Storage, Config, Bridge, Enterprise gateway modules
3. **Phase 3 (Medium)**: CLI, MCP, Plugin, Console omega, App context modules
4. **Phase 4 (Enhancement)**: UI components, i18n, Debug commands, low-priority utils

### Estimated Effort

| Phase | New Tests | Estimated Hours |
|---|---|---|
| Phase 1 | ~1,500 | 120 |
| Phase 2 | ~1,200 | 100 |
| Phase 3 | ~1,000 | 80 |
| Phase 4 | ~800 | 60 |
| **Total** | **~4,500** | **360** |

---

*End of Forge Comprehensive Test Plan*

