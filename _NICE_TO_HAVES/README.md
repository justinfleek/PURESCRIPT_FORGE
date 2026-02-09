# Nice-to-Have Features

This directory contains feature additions that extend beyond the core opencode functionality.
Each feature is self-contained and can be integrated back into the main project when ready.

## Features

| Feature | Description | Status |
|---------|-------------|--------|
| nexus-semantic-network | Semantic network for agent knowledge | Experimental |
| prism-color-system | Theme/color system for terminals/editors | Experimental |
| aleph-build-infrastructure | Nix build tooling and flake modules | Usable |
| render-integration | Render.com deployment integration | Experimental |
| bridge-backend | Backend services (database, analytics) | Experimental |
| compiler-pipeline | PureScript → C++23 → React compiler | Experimental |
| voice-engine | Voice interaction features | Experimental |
| lean-experiments | Experimental Lean4 projects | Research |

## Reintegration

Each feature directory contains:
- `README.md` - Feature description and integration instructions
- `src/` - Source code
- Any other necessary files

To reintegrate a feature:
1. Read the feature's README.md
2. Copy source files to appropriate locations
3. Update flake.nix to include the packages
4. Run tests
5. Update documentation
