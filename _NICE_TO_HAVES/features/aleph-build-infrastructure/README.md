# Aleph - Build Infrastructure

Nix flake modules and build tooling for the FORGE ecosystem.

## Components
- `aleph-b7r6-continuity-0x08/` - Flake modules
  - modules/flake/default - Standard module
  - modules/flake/build - Buck2 build support
  - modules/flake/lre - Local remote execution
  - prelude - Functional prelude for Nix
  - overlays - Nixpkgs overlays

## Integration
Required for advanced build features. Add as flake input:
```nix
aleph-continuity = {
  url = "path:./aleph-b7r6-continuity-0x08";
  inputs.nixpkgs.follows = "nixpkgs";
};
```
