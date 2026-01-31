# Output Format Protocol - How Agents Deliver Information

## Core Principle

**Information must be ACTIONABLE, STRUCTURED, and IMMEDIATELY USABLE.**

Users should be able to:
1. **Understand** what happened (status, summary)
2. **See** what changed (diffs, before/after)
3. **Know** what to do next (actionable steps)
4. **Verify** it worked (verification commands)

---

## Standard Output Structure

### Every Agent Response MUST Follow This Structure:

```markdown
## 📊 STATUS: [SUCCESS/FAILURE/PARTIAL/IN_PROGRESS]

### Summary
[One sentence: What was done and the outcome]

### What Changed
- [File/Component]: [What changed]
- [File/Component]: [What changed]

### Evidence
✅ Verified — [file:line] [what was confirmed]
⚠️ Assumed — [reasoning] [what needs verification]
❓ Needs verification — [what is unknown] [how to verify]

### Next Steps
1. [Actionable step 1]
2. [Actionable step 2]
3. [Actionable step 3]

### Verification
```bash
[Command to verify]
```

### Details
[Expandable details section]
```

---

## Format 1: Code Modification Output

### Example: Fixing a Type Error

```markdown
## 📊 STATUS: SUCCESS

### Summary
Fixed type error in `src/module/File.ts:47` by adding explicit null check.

### What Changed
- `src/module/File.ts:47`: Added null check before accessing `value.property`
- `src/module/File.ts:52`: Updated return type to `Maybe<Result>`

### Before → After

**Before:**
```typescript
function process(value: Value | null): Result {
  return value.property.method(); // ❌ Type error: value may be null
}
```

**After:**
```typescript
function process(value: Value | null): Maybe<Result> {
  if (value === null) {
    return Nothing;
  }
  return Just(value.property.method()); // ✅ Type-safe
}
```

### Evidence
✅ Verified — `src/module/File.ts:47` Type error resolved
✅ Verified — `src/module/File.ts:52` Return type matches implementation
✅ Verified — All callers updated: `src/module/Caller1.ts:23`, `src/module/Caller2.ts:15`

### Files Modified
| File | Lines Changed | Type |
|------|---------------|------|
| `src/module/File.ts` | 47-52 | Fix |
| `src/module/Caller1.ts` | 23 | Update caller |
| `src/module/Caller2.ts` | 15 | Update caller |

### Next Steps
1. ✅ Type check: `npx tsc --noEmit` (already passed)
2. ✅ Tests: `npm test` (already passed)
3. ⏭️ Review changes in your editor
4. ⏭️ Commit: `git add . && git commit -m "Fix: Add null check in process()"`

### Verification
```bash
# Type check
npx tsc --noEmit

# Run tests
npm test

# Lint
npx biome check
```

### Dependency Graph
```
Upstream:
  File.ts ← Value (from types.ts)
  
Downstream:
  File.ts → process() → Caller1.ts
  File.ts → process() → Caller2.ts
```

### Completion Checklist
- [x] All files read completely
- [x] Dependency graph traced
- [x] All instances fixed (3 files)
- [x] No banned constructs
- [x] Types explicit
- [x] Type checks pass
- [x] Tests pass
- [x] Documentation updated
- [x] Workspace clean
```

---

## Format 2: Audit/Validation Output

### Example: Protocol Compliance Audit

```markdown
## 📊 STATUS: FAILURE - 2 CRITICAL Violations Detected

### Summary
Audited 15 agent operations. Found 2 CRITICAL violations, 3 HIGH violations.

### Violations Summary

| Severity | Count | Status |
|----------|-------|--------|
| 🔴 CRITICAL | 2 | BLOCKED |
| 🟠 HIGH | 3 | REQUIRES FIX |
| 🟡 MEDIUM | 5 | WARNING |
| 🟢 LOW | 2 | INFO |

### CRITICAL Violations (BLOCKED)

#### Violation #1: Type Escape
- **Agent:** Deterministic Coder
- **Operation:** Fix type error in `src/module/File.ts`
- **Location:** `src/module/File.ts:47`
- **Violation:** Used `as unknown as Result` (banned construct)
- **Impact:** Type safety compromised, may cause runtime errors
- **Remediation:**
  1. Remove type assertion
  2. Add proper type guard
  3. Update return type
- **Fix:**
  ```typescript
  // ❌ BANNED
  return value as unknown as Result;
  
  // ✅ CORRECT
  if (isResult(value)) {
    return value;
  }
  return defaultResult;
  ```
- **Verification:** `npx tsc --noEmit` must pass without assertions
- **Deadline:** IMMEDIATE (operation blocked)

#### Violation #2: Partial File Read
- **Agent:** Expert Researcher
- **Operation:** Analyze `src/module/LargeFile.ts`
- **Location:** `src/module/LargeFile.ts` (only read lines 1-100)
- **Violation:** Read only 100/2000 lines (5% of file)
- **Impact:** Missing 95% of context, analysis incomplete
- **Remediation:**
  1. Read complete file (all 2000 lines)
  2. Re-run analysis
  3. Update research report
- **Verification:** Verify all 2000 lines were read
- **Deadline:** IMMEDIATE (operation blocked)

### HIGH Violations (REQUIRES FIX)

#### Violation #3: Missing Error Accountability
- **Agent:** Deterministic Coder
- **Operation:** Fix bug in `src/module/Bug.ts`
- **Location:** `src/module/Bug.ts:23`
- **Violation:** Error message: "I apologize for the error" (missing what/why/how/prevention/verification)
- **Remediation:** Add complete error accountability (5 parts)
- **Deadline:** Before next operation

[Continue with other HIGH violations...]

### Action Required

**IMMEDIATE (Blocking):**
1. 🔴 Fix Violation #1: Remove type assertion in `src/module/File.ts:47`
2. 🔴 Fix Violation #2: Re-read complete file `src/module/LargeFile.ts`

**BEFORE NEXT OPERATION:**
3. 🟠 Fix Violation #3: Add error accountability
4. 🟠 Fix Violation #4: [details]
5. 🟠 Fix Violation #5: [details]

### Compliance Score

```
Overall Compliance: 60% (9/15 operations compliant)

By Protocol:
- File Reading:     73% (11/15) ⚠️
- Type Safety:      67% (10/15) ⚠️
- Error Accountability: 80% (12/15) ✅
- Documentation:    87% (13/15) ✅
```

### Remediation Progress

| Violation | Status | Progress |
|-----------|--------|----------|
| #1 | 🔴 BLOCKED | 0% - Not started |
| #2 | 🔴 BLOCKED | 0% - Not started |
| #3 | 🟠 IN PROGRESS | 50% - Partial fix |
| #4 | 🟠 PENDING | 0% - Not started |
| #5 | 🟠 PENDING | 0% - Not started |

### Next Audit
**Scheduled:** [Next audit time]
**Focus:** CRITICAL violations remediation
```

---

## Format 3: Analysis/Research Output

### Example: Code Analysis Report

```markdown
## 📊 STATUS: SUCCESS

### Summary
Analyzed `src/module/ComplexModule.ts` (2000 lines). Found 3 architectural issues, 5 optimization opportunities.

### Key Findings

#### 🔴 Critical Issues (3)

**Issue #1: Circular Dependency**
- **Location:** `ComplexModule.ts` ↔ `DependencyModule.ts`
- **Impact:** Build failures, test flakiness
- **Evidence:**
  - ✅ Verified — `ComplexModule.ts:45` imports `DependencyModule`
  - ✅ Verified — `DependencyModule.ts:67` imports `ComplexModule`
  - ⚠️ Assumed — Circular dependency causes build issues (needs verification)
- **Recommendation:** Extract shared types to `types.ts`
- **Effort:** Medium (2-3 hours)
- **Priority:** HIGH

**Issue #2: Type Escape**
- **Location:** `ComplexModule.ts:123`
- **Impact:** Type safety compromised
- **Evidence:**
  - ✅ Verified — `ComplexModule.ts:123` uses `as unknown as Type`
  - ✅ Verified — Banned construct per protocol
- **Recommendation:** Add type guard instead
- **Effort:** Low (30 minutes)
- **Priority:** CRITICAL

[Continue with other issues...]

#### 🟡 Optimization Opportunities (5)

**Opportunity #1: Memoization**
- **Location:** `ComplexModule.ts:234`
- **Current:** Recomputes expensive calculation on every call
- **Impact:** 10x performance improvement possible
- **Effort:** Low (1 hour)
- **Priority:** MEDIUM

[Continue with other opportunities...]

### Evidence Chain

```
[ComplexModule.ts:45] imports DependencyModule
  → [DependencyModule.ts:67] imports ComplexModule
  → ❌ CIRCULAR DEPENDENCY

[ComplexModule.ts:123] uses 'as unknown as Type'
  → ❌ TYPE ESCAPE (banned construct)
  → [Protocol: banned-constructs.mdc] violation
```

### Recommendations Priority Matrix

| Issue | Priority | Effort | Impact | Recommendation |
|-------|----------|--------|--------|----------------|
| Type Escape | 🔴 CRITICAL | Low | High | Fix immediately |
| Circular Dep | 🟠 HIGH | Medium | High | Fix this sprint |
| Memoization | 🟡 MEDIUM | Low | Medium | Fix when convenient |

### Next Steps

**IMMEDIATE:**
1. Fix type escape in `ComplexModule.ts:123`
   ```typescript
   // Replace: value as unknown as Type
   // With: type guard + narrowing
   ```

**THIS SPRINT:**
2. Break circular dependency (extract shared types)
3. Add memoization to expensive calculation

**FUTURE:**
4. [Other optimizations...]

### Verification

```bash
# Check for circular dependencies
npm run check-deps

# Type check
npx tsc --noEmit

# Performance test
npm run perf-test
```

### Files Analyzed

| File | Lines | Issues Found | Status |
|------|-------|--------------|--------|
| `ComplexModule.ts` | 2000 | 8 | ✅ Complete |
| `DependencyModule.ts` | 500 | 2 | ✅ Complete |
| `types.ts` | 200 | 0 | ✅ Complete |

### Confidence Level

**HIGH** — All files read completely, evidence verified, recommendations based on code analysis.
```

---

## Format 4: Architecture Decision Output

### Example: Architecture Design

```markdown
## 📊 STATUS: SUCCESS

### Summary
Designed architecture for new feature. Selected Approach 3 (Hybrid) after analyzing 3 approaches.

### Decision

**Chosen Approach:** Hybrid Architecture (Approach 3)
**Rationale:** Balances type safety, performance, and maintainability

### Approaches Analyzed

#### Approach 1: Pure Functional
- **Complexity:** Low
- **Maintainability:** High
- **Type Safety:** Strong
- **Performance:** Medium
- **Why Rejected:** Performance not sufficient for use case

#### Approach 2: OOP with Inheritance
- **Complexity:** Medium
- **Maintainability:** Medium
- **Type Safety:** Moderate
- **Performance:** High
- **Why Rejected:** Type safety weaker than required

#### Approach 3: Hybrid (Functional Core + OOP Interface) ✅ CHOSEN
- **Complexity:** Medium
- **Maintainability:** High
- **Type Safety:** Strong
- **Performance:** High
- **Why Chosen:** Best balance of all factors

### Trade-off Matrix

| Dimension | Approach 1 | Approach 2 | Approach 3 |
|-----------|------------|------------|------------|
| Complexity | Low | Medium | Medium |
| Maintainability | High | Medium | High |
| Type Safety | Strong | Moderate | Strong |
| Performance | Medium | High | High |
| Testability | High | Medium | High |

### Trade-offs Accepted

1. **Medium Complexity:** Acceptable for strong type safety
2. **Hybrid Pattern:** More complex than pure functional, but enables performance

### Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Pattern confusion | Medium | Medium | Clear documentation, examples |
| Performance regression | Low | High | Benchmark tests, profiling |

### Implementation Plan

**Phase 1: Core (Week 1)**
- [ ] Implement functional core
- [ ] Add type definitions
- [ ] Write property tests

**Phase 2: Interface (Week 2)**
- [ ] Implement OOP interface
- [ ] Add integration tests
- [ ] Performance benchmarks

**Phase 3: Integration (Week 3)**
- [ ] Integrate with existing system
- [ ] End-to-end tests
- [ ] Documentation

### ADR Created

**File:** `docs/decisions/0042-hybrid-architecture.md`
**Status:** Accepted
**Link:** [ADR-0042](./decisions/0042-hybrid-architecture.md)

### Next Steps

1. Review ADR: `docs/decisions/0042-hybrid-architecture.md`
2. Approve implementation plan
3. Begin Phase 1 implementation
4. Schedule review after Phase 1

### Verification

```bash
# Verify ADR exists
ls docs/decisions/0042-hybrid-architecture.md

# Check ADR links from MASTER.md
grep "ADR-0042" docs/MASTER.md
```
```

---

## Format 5: Network Analysis Output

### Example: Network Graph Analysis

```markdown
## 📊 STATUS: SUCCESS

### Summary
Analyzed network graph with 1,234 nodes and 5,678 edges. Detected 12 communities, identified 5 key bridge nodes.

### Graph Metrics

| Metric | Value | Status |
|--------|-------|--------|
| Nodes | 1,234 | ✅ |
| Edges | 5,678 | ✅ |
| Density | 0.007 | ⚠️ Sparse |
| Avg Degree | 9.2 | ✅ |
| Components | 3 | ⚠️ Disconnected |
| Modularity | 0.65 | ✅ Good |

### Communities Detected (12)

| Community ID | Size | Density | Key Nodes |
|--------------|------|---------|-----------|
| C1 | 234 | 0.12 | node-123, node-456 |
| C2 | 189 | 0.08 | node-789, node-012 |
| C3 | 156 | 0.15 | node-345, node-678 |
| ... | ... | ... | ... |

**Largest Community:** C1 (234 nodes, 19% of network)
**Most Dense:** C3 (density 0.15)

### Key Nodes (Top 10)

| Rank | Node ID | Degree | Betweenness | PageRank | Role |
|------|---------|--------|-------------|----------|------|
| 1 | node-123 | 45 | 0.23 | 0.045 | Hub |
| 2 | node-456 | 38 | 0.19 | 0.038 | Hub |
| 3 | node-789 | 32 | 0.31 | 0.032 | Bridge |
| ... | ... | ... | ... | ... | ... |

### Patterns Discovered

#### Pattern 1: Bridge Nodes (5 nodes)
**Description:** Nodes connecting multiple communities
**Nodes:** node-789, node-234, node-567, node-890, node-123
**Impact:** Critical for information flow
**Recommendation:** Monitor these nodes for changes

#### Pattern 2: Isolated Component (1 component)
**Description:** 3-node component disconnected from main graph
**Nodes:** node-999, node-998, node-997
**Impact:** Information cannot flow to/from main graph
**Recommendation:** Consider adding connections or investigate why isolated

#### Pattern 3: Dense Subgraph (1 subgraph)
**Description:** 15-node clique (fully connected)
**Nodes:** [list of 15 nodes]
**Impact:** High information flow within subgraph
**Recommendation:** May represent tightly-knit group

### Insights

**Structural:**
- Network is sparse but well-connected within communities
- 3 disconnected components suggest potential integration opportunities
- Bridge nodes are critical for cross-community communication

**Dynamic:**
- Network growth rate: +5% nodes/month
- Community stability: High (communities persist over time)
- Bridge node changes: Low (stable bridge structure)

**Functional:**
- Information flow: Efficient within communities, slower between communities
- Key nodes: node-123 and node-789 are critical for network function

### Recommendations

**HIGH PRIORITY:**
1. Monitor bridge nodes (node-789, node-234, etc.) for changes
2. Investigate isolated component (node-999, node-998, node-997)
3. Add connections to isolated component if appropriate

**MEDIUM PRIORITY:**
4. Analyze dense subgraph for special properties
5. Track community evolution over time

**LOW PRIORITY:**
6. Optimize information flow paths
7. Identify potential new bridge nodes

### Visualization Data

```json
{
  "nodes": [...],
  "edges": [...],
  "communities": [...],
  "centrality": {...}
}
```

**Export:** `analysis/network-graph-2026-01-31.json`

### Next Steps

1. Review visualization: `analysis/network-graph-2026-01-31.json`
2. Investigate isolated component
3. Monitor bridge nodes
4. Schedule next analysis: [date]

### Verification

```bash
# Verify analysis file exists
ls analysis/network-graph-2026-01-31.json

# Check report was generated
ls reports/network-analysis-2026-01-31.md
```
```

---

## Format 6: Error/Failure Output

### Example: Operation Failed

```markdown
## 📊 STATUS: FAILURE

### Summary
Operation failed: Type check failed with 3 errors in `src/module/File.ts`.

### What Failed

**Error #1: Type Mismatch**
- **Location:** `src/module/File.ts:47`
- **Error:** `Type 'string | null' is not assignable to type 'string'`
- **Code:**
  ```typescript
  function process(value: string | null): string {
    return value; // ❌ Error: value may be null
  }
  ```

**Error #2: Missing Property**
- **Location:** `src/module/File.ts:89`
- **Error:** `Property 'method' does not exist on type 'Value'`
- **Code:**
  ```typescript
  const result = value.method(); // ❌ Error: method doesn't exist
  ```

[Continue with other errors...]

### Root Cause Analysis

**What:** Type check failed due to 3 type errors
**Why:** 
- Missing null checks (Error #1)
- Incorrect type assumptions (Error #2)
- Missing type definitions (Error #3)

**How:** 
- Code was written without proper type guards
- Types were not verified before implementation

**Prevention:**
- Always add type guards for nullable values
- Verify types match implementation before coding
- Run type check frequently during development

**Verification:**
```bash
# After fixes, verify:
npx tsc --noEmit
```

### Required Fixes

**Fix #1: Add Null Check**
```typescript
// ❌ BEFORE
function process(value: string | null): string {
  return value;
}

// ✅ AFTER
function process(value: string | null): Maybe<string> {
  if (value === null) {
    return Nothing;
  }
  return Just(value);
}
```

**Fix #2: Add Type Guard**
```typescript
// ❌ BEFORE
const result = value.method();

// ✅ AFTER
if (hasMethod(value)) {
  const result = value.method();
}
```

### Next Steps

1. 🔴 Fix Error #1: Add null check in `File.ts:47`
2. 🔴 Fix Error #2: Add type guard in `File.ts:89`
3. 🔴 Fix Error #3: [details]
4. ✅ Verify: Run `npx tsc --noEmit`
5. ✅ Test: Run `npm test`

### Cannot Proceed Until

- [ ] All type errors fixed
- [ ] Type check passes: `npx tsc --noEmit`
- [ ] All tests pass: `npm test`

### Help

**Need help fixing?**
- See: `docs/guides/type-safety.md`
- Example: `docs/examples/null-handling.ts`
- Protocol: `.cursor/rules/type-system.mdc`
```

---

## Universal Output Rules

### 1. Always Include Status
- ✅ SUCCESS: Operation completed successfully
- ❌ FAILURE: Operation failed (with reasons)
- ⚠️ PARTIAL: Some parts succeeded, some failed
- ⏳ IN_PROGRESS: Operation still running

### 2. Always Show Evidence
- ✅ Verified — [file:line] [what was confirmed]
- ⚠️ Assumed — [reasoning] [what needs verification]
- ❓ Needs verification — [what is unknown] [how to verify]

### 3. Always Provide Next Steps
- Numbered, actionable steps
- Clear priorities (🔴 HIGH, 🟠 MEDIUM, 🟡 LOW)
- Commands users can copy/paste

### 4. Always Include Verification
- Commands to verify results
- Expected outputs
- How to confirm it worked

### 5. Always Use Tables for Data
- Structured, scannable
- Sortable columns
- Status indicators (✅ ❌ ⚠️)

### 6. Always Show Before/After for Changes
- Code diffs
- Clear markers (❌ BEFORE, ✅ AFTER)
- Explanation of why change was made

### 7. Always Link to Related Information
- ADRs, documentation, examples
- File paths, line numbers
- Related violations, issues

---

## Output Format Checklist

Before delivering output, verify:

- [ ] Status clearly indicated (SUCCESS/FAILURE/PARTIAL)
- [ ] Summary is one clear sentence
- [ ] What changed is listed (files, lines)
- [ ] Evidence is provided (✅ ⚠️ ❓)
- [ ] Next steps are actionable and numbered
- [ ] Verification commands are provided
- [ ] Tables used for structured data
- [ ] Before/after shown for changes
- [ ] Links to related information
- [ ] Completion checklist included (if applicable)

---

**This protocol applies to ALL agents. Every output must follow this structure.**
