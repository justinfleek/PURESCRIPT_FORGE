# OpenCode Parity Tracker

## Overview

| Metric | OpenCode (TS) | COMPASS (PS) | Gap |
|--------|---------------|--------------|-----|
| **Total Lines** | 28,234 | ~36,000 | +7,766 (extra infra) |
| **Stubs Remaining** | 0 | 452 | 452 to implement |
| **Core Modules** | 20 | 20 | Types exist, impl varies |

## Module-by-Module Parity

### Priority 1: Core Engine (Must Have)

| Module | OpenCode Lines | COMPASS Lines | Stubs | Parity | Notes |
|--------|----------------|---------------|-------|--------|-------|
| `provider/` | 5,436 | 1,289 | 30 | **20%** | Missing: AI SDK abstraction, 20+ provider loaders, models.dev integration |
| `session/` | 4,999 | 1,625 | 33 | **35%** | Missing: SQLite persistence, proper message handling, compaction |
| `tool/` | 3,528 | 6,883 | 39 | **75%** | Core tools implemented, missing: proper sandbox execution |
| `permission/` | 653 | 432 | 0 | **80%** | Types exist, need interactive flow |

### Priority 2: Server & API (Must Have)

| Module | OpenCode Lines | COMPASS Lines | Stubs | Parity | Notes |
|--------|----------------|---------------|-------|--------|-------|
| `server/` | 3,511 | 715 | 49 | **25%** | Routes stubbed, need OpenAPI compliance |
| `config/` | 1,511 | 165 | 2 | **15%** | Need full opencode.json parsing |
| `auth/` | N/A | 839 | 0 | **90%** | OAuth flows exist in auth/ |

### Priority 3: Integrations (Should Have)

| Module | OpenCode Lines | COMPASS Lines | Stubs | Parity | Notes |
|--------|----------------|---------------|-------|--------|-------|
| `lsp/` | 2,902 | ~400 | 4 | **15%** | Language server protocol integration |
| `mcp/` | 1,420 | ~200 | N/A | **10%** | Model Context Protocol |
| `plugin/` | 1,049 | 199 | 8 | **20%** | Plugin loading system |
| `file/` | 1,109 | 205 | 10 | **20%** | File operations |

### Priority 4: CLI & TUI (Nice to Have)

| Module | OpenCode Lines | COMPASS Lines | Stubs | Parity | Notes |
|--------|----------------|---------------|-------|--------|-------|
| `cli/` | 7,027 | 974 | 112 | **15%** | Commands mostly stubbed |
| `acp/` | 1,707 | N/A | N/A | **0%** | Agent Communication Protocol |

---

## Critical Gaps to Close

### 1. Provider System (provider.ts - 1,220 lines)

**OpenCode Features:**
- [ ] Dynamic SDK loading via `BunProc.install()`
- [ ] 20+ bundled providers (Anthropic, Azure, Bedrock, etc.)
- [ ] Custom loaders per provider (auth, headers, model selection)
- [ ] models.dev API integration for model metadata
- [ ] SDK caching with hash key
- [ ] `getLanguage()` returns AI SDK `LanguageModelV2`

**COMPASS Status:**
- [x] Basic registry with 3 hardcoded providers
- [ ] No dynamic loading
- [ ] No models.dev integration
- [ ] Direct HTTP instead of AI SDK abstraction

### 2. Session System (session/*.ts - 4,999 lines)

**OpenCode Features:**
- [ ] `Session.create()`, `Session.get()`, `Session.list()`
- [ ] SQLite persistence via Drizzle ORM
- [ ] Message parts system (text, tool calls, images)
- [ ] Compaction for long conversations
- [ ] Summary generation
- [ ] Branching (parent sessions)
- [ ] Token usage tracking
- [ ] `Processor.ts` agentic loop with parallel tool execution

**COMPASS Status:**
- [x] Basic Processor with sequential tool execution
- [x] LLM.purs with HTTP calls
- [ ] No persistence
- [ ] No compaction
- [ ] No branching

### 3. AI SDK Abstraction

**OpenCode Uses:**
```typescript
import { streamText, generateText } from 'ai'
import { createAnthropic } from '@ai-sdk/anthropic'

const model = await Provider.getLanguage(modelInfo)
const result = await streamText({
  model,
  messages,
  tools,
  onChunk: (chunk) => { ... }
})
```

**COMPASS Needs:**
```purescript
-- Need to implement LanguageModelV2 interface
class LanguageModel m where
  doGenerate :: m -> GenerateParams -> Aff GenerateResult
  doStream :: m -> StreamParams -> Aff (Stream Chunk)

-- Then provider-specific implementations
anthropicModel :: AnthropicConfig -> LanguageModel
openaiModel :: OpenAIConfig -> LanguageModel
```

### 4. Tool Execution (tool/*.ts - 3,528 lines)

**OpenCode Features:**
- [ ] Parallel tool execution in batches
- [ ] Tool permission approval flow
- [ ] Output truncation with file fallback
- [ ] Tool result formatting
- [ ] Metadata tracking

**COMPASS Status:**
- [x] Sequential execution
- [x] Basic permission check
- [ ] No parallel execution
- [ ] Truncation exists but not wired

---

## Implementation Order

### Phase 1: Provider Parity (Est. 2,000 lines)
1. Port `provider/provider.ts` fully
2. Implement custom loaders for top 5 providers
3. Add models.dev API integration
4. Create LanguageModel typeclass

### Phase 2: Session Parity (Est. 1,500 lines)
1. Port `session/session.ts` with SQLite
2. Implement message parts properly
3. Add compaction/summary
4. Wire Processor with parallel execution

### Phase 3: Server Parity (Est. 1,000 lines)
1. Complete all route handlers
2. OpenAPI spec compliance
3. WebSocket events

### Phase 4: CLI Parity (Est. 2,000 lines)
1. Port each command
2. TUI components

---

## Files to Port (Priority Order)

### Immediate (Provider)
1. `_OTHER/opencode-original/packages/opencode/src/provider/provider.ts` (1,220 lines)
2. `_OTHER/opencode-original/packages/opencode/src/provider/models.ts` (238 lines)
3. `_OTHER/opencode-original/packages/opencode/src/provider/transform.ts` (178 lines)

### Immediate (Session)
1. `_OTHER/opencode-original/packages/opencode/src/session/session.ts` (520 lines)
2. `_OTHER/opencode-original/packages/opencode/src/session/message.ts` (600 lines)
3. `_OTHER/opencode-original/packages/opencode/src/session/processor.ts` (1,100 lines)

### Next (Tools)
1. `_OTHER/opencode-original/packages/opencode/src/tool/tool.ts` (400 lines)
2. `_OTHER/opencode-original/packages/opencode/src/tool/bash.ts` (500 lines)

---

## Reference Locations

- **OpenCode Source**: `_OTHER/opencode-original/packages/opencode/src/`
- **OpenCode OpenAPI**: `_OTHER/opencode-original/packages/sdk/openapi.json`
- **COMPASS Source**: `COMPASS/src/opencode/`
- **Bridge FFI**: `COMPASS/src/opencode/bridge/ps/Bridge/FFI/`
