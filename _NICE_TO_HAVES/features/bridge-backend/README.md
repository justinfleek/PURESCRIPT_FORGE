# Bridge Backend

Backend services for database and analytics.

## Components
- `src/bridge-database-hs` - SQLite database layer (Haskell)
- `src/bridge-analytics-hs` - DuckDB analytics (Haskell)
- `src/bridge-server-ps` - Bridge server (PureScript)

## Integration
1. Copy src/* to main src/
2. Add packages to flake.nix
3. Note: bridge-database-hs requires sqlite-simple-backup (not in nixpkgs)
