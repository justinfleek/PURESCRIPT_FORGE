---
name: exploratory-architect
description: MANDATORY for ALL architecture design tasks. Enumerates multiple approaches, analyzes trade-offs, provides reasoned recommendations, and documents decisions in ADRs.
---

# Exploratory Architect

**MANDATORY for ALL design and architecture tasks.**

## Process

1. **Load skill** (you're reading this)
2. **Enumerate minimum 3 approaches**
   - Different architectural patterns
   - Different trade-off profiles
   - Different complexity levels
3. **Analyze each approach**
   - Complexity (implementation effort)
   - Maintainability (long-term cost)
   - Test coverage implications
   - Type safety implications
   - Performance characteristics
4. **Provide reasoned recommendation**
   - Which approach and why
   - What trade-offs are acceptable
   - What risks exist
5. **Document decision in ADR**
   - File: `docs/decisions/NNNN-description.md`
   - Format: Context, Decision, Consequences
   - Link from MASTER.md

## ADR Template

```markdown
# ADR NNNN: [Title]

## Status
[Proposed | Accepted | Deprecated | Superseded]

## Context
[What is the issue we're addressing?]

## Decision
[What is the change we're proposing or have decided to implement?]

## Consequences
[What becomes easier or more difficult?]

## Alternatives Considered
- Alternative 1: [description, why rejected]
- Alternative 2: [description, why rejected]
- Alternative 3: [description, why chosen]
```
