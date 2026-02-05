# gVisor, AST Edit, and SearXNG Implementation Status

## Overview

This document tracks the implementation status of three critical systems:
1. **gVisor** - Container security sandbox
2. **AST Edit** - Abstract Syntax Tree editing capabilities
3. **SearXNG** - Privacy-respecting metasearch engine integration

---

## ✅ Completed

### 1. gVisor FFI Implementation

**Files Created:**
- `COMPASS/src/opencode/aleph/Sandbox/GVisor.FFI.purs` - PureScript FFI interface
- `COMPASS/src/opencode/aleph/Sandbox/GVisor.FFI.js` - Node.js implementation

**Features Implemented:**
- ✅ Container lifecycle management (create, start, exec, kill, delete)
- ✅ OCI bundle creation from ContainerConfig
- ✅ Container status queries
- ✅ Integration with `GVisor.purs` runtime management

**Key Functions:**
- `createContainer` - Creates gVisor container from OCI bundle
- `startContainer` - Starts a created container
- `execInContainer` - Executes commands in running container
- `killContainer` - Kills running container
- `deleteContainer` - Deletes stopped container
- `listContainers` - Lists all containers
- `getContainerStatus` - Gets container status

**Integration Points:**
- `GVisor.purs` now uses FFI for all runtime operations
- `createRuntime` and `destroyRuntime` fully implemented
- `execute` function now uses `execInContainer` FFI

### 2. SearXNG HTTP Client Implementation

**Files Created:**
- `COMPASS/src/opencode/tool/Search/SearXNG.FFI.purs` - PureScript FFI interface
- `COMPASS/src/opencode/tool/Search/SearXNG.FFI.js` - Node.js HTTP client

**Features Implemented:**
- ✅ HTTP GET requests with timeout support
- ✅ JSON response parsing
- ✅ SearXNG API response transformation
- ✅ Error handling for HTTP and JSON parsing

**Key Functions:**
- `httpGet` - Basic HTTP GET request
- `httpGetWithTimeout` - HTTP GET with custom timeout
- `performSearch` - Full search request to SearXNG
- `parseResponse` - Parse SearXNG JSON response
- `parseSearXNGResponse` - Transform JSON to SearchResult type

**Integration Points:**
- `SearXNG.purs` now fully implements search functionality
- Response parsing handles all SearXNG result types (web, images, videos, etc.)
- Proper error handling throughout

---

## 🚧 In Progress

### 3. AST Edit Implementation

**Status:** Parser FFI in progress

**Files to Create:**
- `COMPASS/src/opencode/tool/ASTEdit/Structural.FFI.purs` - Parser FFI interface
- `COMPASS/src/opencode/tool/ASTEdit/Structural.FFI.js` - Tree-sitter/parser bindings

**Required Parsers:**
- Tree-sitter (TypeScript, Nix)
- PureScript parser (via purescript compiler)
- Haskell parser (via ghc-lib)
- Lean4 parser (via Lean4 API)

**Operations to Implement:**
- `Rename` - Symbol renaming with scope awareness
- `Extract` - Extract code span to binding
- `Inline` - Inline all occurrences of symbol
- `Reorder` - Reorder declarations
- `Wrap` - Wrap span in construct (let, do, case, etc.)
- `Unwrap` - Remove wrapper construct
- `AddImport` - Add import statement
- `RemoveUnused` - Remove unused bindings
- `Hole` - Replace with typed hole
- `MoveToFile` - Move declaration to different file

---

## 📋 Pending Tasks

### 1. gVisor Integration into NEXUS

**Task:** Replace bubblewrap with gVisor in NEXUS agent orchestrator

**Files to Modify:**
- `NEXUS/agent-orchestrator/src/sandbox_manager.py` - Replace bubblewrap with gVisor
- `NEXUS/agent-orchestrator-ps/src/Nexus/AgentOrchestrator/Sandbox.purs` - Update PureScript bindings

**Steps:**
1. Create gVisor wrapper in Python/PureScript
2. Update sandbox profiles to use gVisor configs
3. Migrate agent launch logic to use gVisor
4. Test agent isolation with gVisor

### 2. SearXNG Integration into NEXUS Web Search Agent

**Task:** Replace DuckDuckGo/Google with SearXNG in web search agent

**Files to Modify:**
- `NEXUS/web-search-agent/src/search_executor.py` - Add SearXNG support
- Update agent to use SearXNG API

**Steps:**
1. Add SearXNG client to Python search executor
2. Configure SearXNG instance URL
3. Update search agent to use SearXNG
4. Test search functionality

### 3. AST Edit Parser Implementation

**Task:** Implement language parsers via FFI

**Approach:**
- **Tree-sitter** (TypeScript, Nix): Use `tree-sitter` npm package
- **PureScript**: Use PureScript compiler API or `purescript-ast` library
- **Haskell**: Use `ghc-lib-parser` or `haskell-src-exts`
- **Lean4**: Use Lean4 LSP or parser API

**Files to Create:**
- `ASTEdit/Structural/FFI/Parser.purs` - Parser interface
- `ASTEdit/Structural/FFI/Parser.js` - Parser implementations

### 4. AST Edit Transformations

**Task:** Implement all transformation operations

**Operations:**
- Rename with scope tracking
- Extract with dependency analysis
- Inline with safety checks
- Reorder with dependency resolution
- Wrap/Unwrap with syntax preservation
- Import management
- Unused binding detection
- Typed hole generation
- Cross-file moves

### 5. Testing

**Task:** Add comprehensive tests

**Test Types:**
- Unit tests for each FFI function
- Property tests for AST transformations
- Integration tests for gVisor container lifecycle
- Integration tests for SearXNG search
- End-to-end tests for agent isolation

---

## 🔧 Technical Details

### gVisor Architecture

```
Host Kernel
  ├── runsc (control plane)
  ├── Gofer (9P proxy)
  └── Sentry (syscall intercept)
      └── Sandboxed Process
```

**Platforms Supported:**
- KVM (hardware virtualization) - Best performance
- PTRACE (ptrace-based) - Most compatible
- SYSTRAP (syscall trap) - Good balance

### SearXNG Architecture

```
SearXNG Instance
  ├── Aggregates from 70+ engines
  ├── Deduplicates results
  ├── Scores and ranks
  └── Returns JSON/RSS/CSV
```

**Privacy Features:**
- No user tracking
- IP address hidden from engines
- No search history
- Self-hostable

### AST Edit Architecture

```
Source Code
  ├── Parse to AST (language-specific)
  ├── Transform AST (structural operations)
  ├── Validate (syntax, types, scopes)
  └── Render to Source (preserve formatting)
```

**Guarantees:**
- Syntax preservation
- Scope awareness
- Comment attachment
- Formatting preservation

---

## 📝 Next Steps

1. **Complete AST Edit Parsers** - Implement FFI for all language parsers
2. **Implement AST Transformations** - Complete all structural edit operations
3. **Integrate gVisor into NEXUS** - Replace bubblewrap with gVisor
4. **Integrate SearXNG into NEXUS** - Update web search agent
5. **Add Comprehensive Tests** - Unit, property, and integration tests

---

## 🎯 Success Criteria

- ✅ gVisor containers can be created, started, and managed
- ✅ SearXNG searches return properly parsed results
- ⏳ AST Edit can parse all supported languages
- ⏳ AST Edit can perform all transformation operations
- ⏳ NEXUS agents run in gVisor sandboxes
- ⏳ NEXUS web search uses SearXNG
- ⏳ All systems have comprehensive test coverage
