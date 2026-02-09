# NEXUS - Semantic Network

Agent-based semantic network for knowledge management and retrieval.

## Components
- `NEXUS/` - Main NEXUS implementation
  - agent-orchestrator - Agent coordination
  - semantic-cells - Knowledge units
  - network-graph - Graph operations
  - database-layer - Persistence
  - bridge-server-ps - PureScript bridge
  - proofs-lean - Formal proofs

## Integration
1. Copy NEXUS/ to project root
2. Add packages to flake.nix (see original flake.nix for examples)
3. Wire up to main opencode session management
