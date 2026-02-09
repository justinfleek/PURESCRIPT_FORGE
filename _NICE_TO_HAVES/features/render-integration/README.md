# Render Integration

Integration with Render.com for deployment and GPU inference.

## Components
- `src/render-api-ps` - API client (PureScript)
- `src/render-gateway-hs` - Inference gateway (Haskell)
- `src/render-billing-hs` - GPU billing
- `src/render-cas-hs` - Content-addressable storage
- `src/render-clickhouse-hs` - Analytics
- `src/render-compliance-hs` - Audit trail
- `src/render-config-dhall` - Configuration

## Integration
1. Copy src/* to main src/
2. Add packages to flake.nix
3. Configure Render.com credentials
