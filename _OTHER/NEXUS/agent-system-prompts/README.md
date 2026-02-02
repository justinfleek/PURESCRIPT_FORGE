# NEXUS Agent System Prompts

This directory contains **perfect agentic system prompts** that use the PURESCRIPT_FORGE protocols and system perfectly.

## Created System Prompts

### 1. Deterministic Coder Agent (`01-deterministic-coder.md`)
**Purpose:** MANDATORY for ALL code modifications

**Key Features:**
- Complete file reading protocol (no grep, no partial reads)
- Type safety enforcement (no banned constructs)
- Error accountability (what, why, how, prevention, verification)
- Systematic debugging protocol (reproduce, trace, isolate, fix, verify, prevent)
- Documentation protocol (every operation updates docs)
- Continuity protocol (session/build/type/documentation continuity)
- Language stack compliance (PureScript/Haskell/Lean4 only)
- Task completion criteria (all boxes must be checked)

**Use When:** Any code modification task

---

### 2. Exploratory Architect Agent (`02-exploratory-architect.md`)
**Purpose:** MANDATORY for ALL architecture design tasks

**Key Features:**
- Minimum 3 approaches required (different patterns, trade-offs, complexity)
- Systematic analysis (complexity, maintainability, testability, type safety, performance, security)
- Trade-off matrix (explicit comparison of all approaches)
- Type safety analysis (no type escapes allowed)
- ADR documentation (Context, Decision, Consequences, Alternatives)
- Evidence-based recommendations (file:line references)
- NEXUS-specific considerations (sandbox compatibility, agent communication)

**Use When:** Architecture design, system design, technology choices

---

### 3. Expert Researcher Agent (`03-expert-researcher.md`)
**Purpose:** Research and analysis tasks requiring synthesis from multiple sources

**Key Features:**
- Complete file reading protocol (no grep, no partial reads)
- Evidence classification (✅ Verified, ⚠️ Assumed, ❓ Needs verification)
- Dependency tracing (upstream and downstream)
- Documentation verification (verify docs against code)
- Evidence chain building (Verified → Assumed → Conclusion)
- Research report format (structured, evidence-based)
- External source handling (cite, verify, classify)

**Use When:** Research tasks, code analysis, documentation verification

---

### 4. NEXUS Web Search Agent (`04-nexus-web-search-agent.md`)
**Purpose:** Autonomous web search agent operating in NEXUS sandbox

**Key Features:**
- Sandbox constraints (allowed/denied directories, network access)
- Query generation (from semantic cells, priority-based)
- Web search execution (DuckDuckGo/Google, error handling)
- Link following (content fetching, link extraction)
- Content storage (organized, metadata-preserved)
- Error accountability (what, why, how, prevention, verification)
- Logging & monitoring (structured logs, no sensitive data)
- Performance requirements (rate limits, timeouts, concurrency)

**Use When:** Web search operations, content fetching, semantic cell query generation

---

## Output Format Protocol

**CRITICAL:** All agents MUST follow the Output Format Protocol (`OUTPUT_FORMAT_PROTOCOL.md`)

### Key Requirements

Every agent output MUST include:
- ✅ **Status** (SUCCESS/FAILURE/PARTIAL/IN_PROGRESS)
- ✅ **Summary** (one clear sentence)
- ✅ **What Changed** (files, lines, changes)
- ✅ **Evidence** (✅ Verified / ⚠️ Assumed / ❓ Needs verification)
- ✅ **Next Steps** (actionable, numbered, prioritized)
- ✅ **Verification** (commands to verify results)
- ✅ **Tables** (for structured data)
- ✅ **Before/After** (for code changes)

### Output Examples

See `OUTPUT_FORMAT_PROTOCOL.md` for:
- Format 1: Code Modification Output (with diffs)
- Format 2: Audit/Validation Output (with violations table)
- Format 3: Analysis/Research Output (with findings)
- Format 4: Architecture Decision Output (with trade-offs)
- Format 5: Network Analysis Output (with metrics tables)
- Format 6: Error/Failure Output (with root cause)

**All agents deliver information in structured, actionable formats that users can immediately act upon.**

---

## Protocol Integration

All system prompts integrate the core PURESCRIPT_FORGE protocols:

- ✅ **Core Principles:** ACCURACY > SPEED, COMPLETENESS > CONVENIENCE
- ✅ **File Reading:** Complete reads only, no grep/partial reads
- ✅ **Type Safety:** No banned constructs, explicit types
- ✅ **Error Accountability:** What, why, how, prevention, verification
- ✅ **Debugging:** Reproduce, trace, isolate, fix, verify, prevent
- ✅ **Documentation:** Every operation updates docs
- ✅ **Continuity:** Session/build/type/documentation continuity
- ✅ **Language Stack:** PureScript/Haskell/Lean4 only
- ✅ **Execution Standards:** Correct and slow > fast and wrong

---

## Usage

Each system prompt is self-contained and can be used directly as a system prompt for an AI agent. They are designed to be:

1. **Complete:** All necessary protocols integrated
2. **Precise:** No ambiguity, clear requirements
3. **Enforceable:** Clear failure modes and recovery
4. **Evidence-based:** Every claim requires evidence
5. **Documented:** Every operation updates documentation

---

### 5. Protocol Enforcer Agent (`05-protocol-enforcer-agent.md`)
**Purpose:** Meta-agent that audits and ensures all other agents follow protocols

**Key Features:**
- Audits all agents for protocol compliance
- Detects violations (CRITICAL, HIGH, MEDIUM, LOW)
- Enforces remediation (blocks, requires fixes, warns)
- Generates audit reports (real-time, hourly, daily, weekly)
- Tracks remediation progress
- Suggests protocol improvements

**Use When:** Continuous compliance monitoring, agent auditing

---

### 6. Type Safety Guardian (`06-type-safety-guardian.md`)
**Purpose:** Validates and enforces type safety across entire codebase

**Key Features:**
- Detects banned constructs (`any`, `unknown`, `as Type`, etc.)
- Verifies type completeness (explicit types at boundaries)
- Verifies type correctness (types match implementation)
- Verifies totality (all functions total, no partial functions)
- Verifies type safety continuity (no type escapes)
- Generates violation reports with remediation

**Use When:** Type safety audits, code reviews, pre-commit checks

---

### 7. Proof Generator Agent (`07-proof-generator-agent.md`)
**Purpose:** Generates Lean4 proofs for critical invariants

**Key Features:**
- Identifies proof requirements (critical invariants, safety properties)
- Generates proofs (by construction, induction, contradiction, cases)
- Verifies proofs (compiles, checks, complete, documented)
- Organizes proofs (directory structure, naming conventions)
- Maintains proofs (updates when code changes)
- Tracks proof dependencies

**Use When:** Critical invariant verification, formal verification, proof maintenance

---

### 8. Semantic Memory Architect (`08-semantic-memory-architect.md`)
**Purpose:** Designs and optimizes semantic cell structures and couplings

**Key Features:**
- Designs semantic cells (identity, level, domain, basin, state)
- Designs couplings (types, strengths, bidirectional)
- Optimizes hierarchies (acyclic, well-formed, balanced)
- Initializes state (position, velocity, energy, grade)
- Verifies semantic coherence (cells, couplings, hierarchies, state)
- Optimizes structures (retrieval efficiency, similarity accuracy)

**Use When:** Semantic memory design, knowledge structure optimization, cell creation

---

### 9. Network Analyst Agent (`09-network-analyst-agent.md`)
**Purpose:** Analyzes network graphs, discovers patterns, provides insights

**Key Features:**
- Analyzes graph structure (metrics, connectivity, degree distribution)
- Detects communities (Louvain, Leiden, label propagation)
- Computes centrality (degree, betweenness, closeness, PageRank)
- Discovers patterns (clustering, bridges, isolation, dense subgraphs)
- Tracks evolution (node/edge changes, community changes)
- Generates insights (structural, dynamic, functional)
- Provides recommendations

**Use When:** Network graph analysis, pattern discovery, community detection, centrality analysis

---

## Next Steps

Additional system prompts to create:

- [ ] NEXUS Content Extraction Agent
- [ ] NEXUS Network Formation Agent
- [ ] NEXUS Database Layer Agent
- [ ] NEXUS Agent Social Agent
- [ ] NEXUS Agent Orchestrator
- [ ] CRDT Validator Agent (validates CRDT merge operations)
- [ ] Refactoring Strategist Agent (plans safe refactorings)
- [ ] Test Generator Agent (generates property tests)
- [ ] Migration Planner Agent (plans TypeScript → PureScript migrations)
- [ ] Performance Profiler Agent (analyzes performance, suggests optimizations)

---

## Maintenance

When updating protocols:

1. Update relevant system prompts
2. Verify protocol integration
3. Test with example scenarios
4. Update this README

---

**Last Updated:** 2026-01-31
**Status:** ✅ 9 agents complete (4 core + 1 NEXUS + 4 creative meta-agents)
