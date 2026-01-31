# Agent Configuration

This file configures agent behavior for the PURESCRIPT_FORGE workspace.

## Skills

### Required Skills

Before performing tasks, agents MUST load appropriate skills:

- **deterministic-coder**: MANDATORY for ALL code modifications
- **exploratory-architect**: MANDATORY for ALL architecture design tasks
- **expert-researcher**: Use for research and analysis tasks

## Rules

All rules in `.cursor/rules/` apply. Key rules:

- **core-principles.mdc**: Accuracy > Speed, Code is Truth
- **file-reading-protocol.mdc**: Complete reads only, no grep
- **banned-constructs.mdc**: No type escapes, no shortcuts
- **type-system.mdc**: Types describe, code is truth
- **error-accountability.mdc**: Root cause analysis required
- **execution-standards.mdc**: Correct and slow > fast and wrong
- **documentation-protocol.mdc**: Every operation updates docs
- **continuity-protocol.mdc**: Session/build/type/documentation continuity
- **build-verification.mdc**: Nix-based builds, post-build validation
- **ci-cd-patterns.mdc**: Reproducible builds, validation gates
- **testing-standards.mdc**: Property tests, deterministic tests
- **haskell-standards.mdc**: Strict compiler flags, property tests (Haskell files)
- **nix-standards.mdc**: Reproducible builds, flake structure (Nix files)

## Project Structure

```
PURESCRIPT_FORGE/
├── .cursor/
│   ├── rules/          # Project rules
│   └── skills/         # Project skills
├── docs/               # Documentation
│   ├── MASTER.md       # System overview
│   ├── architecture/   # Component docs
│   ├── decisions/      # ADRs
│   └── changelog/      # Change log
├── opencode-dev/       # TypeScript/Bun project (migration target)
└── trtllm-serve-main/  # Nix/Haskell reference standard
```

## Migration Goals

The `opencode-dev` project will be migrated to match `trtllm-serve-main` standards:

- Type safety (PureScript/Haskell/Lean4 where applicable)
- Nix-based reproducible builds
- Strict type checking
- Complete file reading protocol
- No banned constructs
- Comprehensive documentation

## Verification

Before any task completion:
- [ ] All files read completely
- [ ] Dependency graph traced
- [ ] All instances fixed across codebase
- [ ] No banned constructs
- [ ] Types explicit
- [ ] Type checks pass
- [ ] Tests pass
- [ ] Documentation updated
- [ ] Workspace clean
