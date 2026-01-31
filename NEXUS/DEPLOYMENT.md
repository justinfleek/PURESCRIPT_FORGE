# Nexus Fly.io Deployment Guide

## Overview

This guide covers deploying the Nexus system to Fly.io with multi-region support, PostgreSQL replication, and edge-native agent execution.

## Prerequisites

1. **Fly.io Account**: Sign up at https://fly.io
2. **Fly CLI**: Install from https://fly.io/docs/hands-on/install-flyctl/
3. **Authentication**: Run `flyctl auth login`
4. **PostgreSQL Password**: Generate a secure password for PostgreSQL

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Fly.io Multi-Region                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │
│  │   Region 1   │  │   Region 2   │  │   Region 3   │  │
│  │   (iad)      │  │   (lhr)       │  │   (nrt)       │  │
│  │              │  │              │  │              │  │
│  │ Bridge Server│  │ Bridge Server│  │ Bridge Server│  │
│  │              │  │              │  │              │  │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘  │
│         │                  │                  │          │
│         └──────────────────┼──────────────────┘          │
│                            │                              │
│                    ┌───────▼───────┐                      │
│                    │  PostgreSQL   │                      │
│                    │  (Primary)    │                      │
│                    │  (iad)        │                      │
│                    └───────┬───────┘                      │
│                            │                              │
│                    ┌───────▼───────┐                      │
│                    │   Replicas    │                      │
│                    │  (lhr, nrt)   │                      │
│                    └───────────────┘                      │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## Deployment Steps

### 1. Initial Setup

```bash
# Clone repository
cd NEXUS

# Make deployment script executable
chmod +x deploy.sh

# Set PostgreSQL password (or generate one)
export POSTGRES_PASSWORD=$(openssl rand -base64 32)

# Set Fly.io API token (optional, for agent orchestration)
export FLY_API_TOKEN="your-fly-api-token"
```

### 2. Deploy PostgreSQL Cluster

```bash
# Create PostgreSQL app
flyctl apps create nexus-postgres --org personal

# Deploy PostgreSQL to primary region
flyctl deploy --config fly.postgres.toml --app nexus-postgres --region iad

# Create persistent volume
flyctl volumes create nexus_postgres_data --app nexus-postgres --region iad --size 10

# Set PostgreSQL password secret
flyctl secrets set "POSTGRES_PASSWORD=$POSTGRES_PASSWORD" --app nexus-postgres

# Get database URL
flyctl config show --app nexus-postgres
```

### 3. Deploy Bridge Server

```bash
# Create Bridge Server app
flyctl apps create nexus-bridge-server --org personal

# Set secrets
flyctl secrets set "DATABASE_URL=postgresql://nexus:password@nexus-postgres.internal:5432/nexus?sslmode=require" --app nexus-bridge-server
flyctl secrets set "FLY_API_TOKEN=$FLY_API_TOKEN" --app nexus-bridge-server

# Deploy to primary region
cd bridge-server-ps
flyctl deploy --config ../fly.toml --app nexus-bridge-server --region iad

# Deploy to additional regions
for region in lhr nrt sjc; do
  flyctl deploy --config ../fly.toml --app nexus-bridge-server --region $region
done
```

### 4. Automated Deployment

Use the provided deployment script:

```bash
./deploy.sh
```

This script will:
- Check prerequisites
- Create PostgreSQL cluster
- Create Bridge Server app
- Configure secrets
- Deploy to all regions
- Set up health checks
- Scale instances
- Verify deployment

## Configuration

### Environment Variables

**Bridge Server:**
- `DATABASE_URL`: PostgreSQL connection string
- `FLY_API_TOKEN`: Fly.io API token for agent orchestration
- `REGION`: Current region identifier (set per machine)
- `PORT`: HTTP server port (default: 8080)
- `LOG_LEVEL`: Logging level (default: info)

**PostgreSQL:**
- `POSTGRES_USER`: Database user (default: nexus)
- `POSTGRES_DATABASE`: Database name (default: nexus)
- `POSTGRES_PASSWORD`: Database password (set via secrets)

### Secrets Management

```bash
# Set secrets for Bridge Server
flyctl secrets set "DATABASE_URL=..." --app nexus-bridge-server
flyctl secrets set "FLY_API_TOKEN=..." --app nexus-bridge-server

# Set secrets for PostgreSQL
flyctl secrets set "POSTGRES_PASSWORD=..." --app nexus-postgres

# List secrets
flyctl secrets list --app nexus-bridge-server

# Remove secret
flyctl secrets unset SECRET_NAME --app nexus-bridge-server
```

## Health Checks

Health checks are configured in `fly.toml`:

```toml
[[http_service.checks]]
  grace_period = "10s"
  interval = "30s"
  method = "GET"
  timeout = "5s"
  path = "/health"
```

The Bridge Server exposes a `/health` endpoint that:
- Returns `200 OK` if the server is running
- Checks PostgreSQL connectivity (if `DATABASE_URL` is set)

## Scaling

### Manual Scaling

```bash
# Scale Bridge Server to 2 instances in a region
flyctl scale count 2 --app nexus-bridge-server --region iad

# Scale PostgreSQL (primary)
flyctl scale count 1 --app nexus-postgres --region iad
```

### Auto-Scaling

Auto-scaling is configured in `fly.toml`:

```toml
[scaling]
  min_instances = 1
  max_instances = 10
  target_cpu_percent = 70
```

## Monitoring

### View Logs

```bash
# Bridge Server logs
flyctl logs --app nexus-bridge-server

# PostgreSQL logs
flyctl logs --app nexus-postgres

# Region-specific logs
flyctl logs --app nexus-bridge-server --region iad
```

### Check Status

```bash
# Bridge Server status
flyctl status --app nexus-bridge-server

# PostgreSQL status
flyctl status --app nexus-postgres

# List all apps
flyctl apps list
```

### Metrics

Fly.io provides built-in metrics:
- CPU usage
- Memory usage
- Request latency
- Error rates

Access via Fly.io dashboard or API.

## Load Testing

Run the provided load testing script:

```bash
chmod +x load-test.sh
./load-test.sh
```

This will test:
- Latency to each region
- Concurrent throughput
- Agent launch performance

## Rollback Procedures

### Rollback Bridge Server

```bash
# List releases
flyctl releases --app nexus-bridge-server

# Rollback to previous release
flyctl releases rollback <release-id> --app nexus-bridge-server
```

### Rollback PostgreSQL

**⚠️ Warning**: Rolling back PostgreSQL can cause data loss. Always backup before rollback.

```bash
# List releases
flyctl releases --app nexus-postgres

# Rollback (use with caution)
flyctl releases rollback <release-id> --app nexus-postgres
```

### Emergency Rollback

```bash
# Stop all instances
flyctl scale count 0 --app nexus-bridge-server

# Restart with previous image
flyctl releases rollback <previous-release-id> --app nexus-bridge-server

# Scale back up
flyctl scale count 1 --app nexus-bridge-server
```

## Troubleshooting

### Bridge Server Not Starting

1. Check logs: `flyctl logs --app nexus-bridge-server`
2. Verify secrets: `flyctl secrets list --app nexus-bridge-server`
3. Check health endpoint: `curl https://nexus-bridge-server.fly.dev/health`

### PostgreSQL Connection Issues

1. Verify `DATABASE_URL` secret is set correctly
2. Check PostgreSQL status: `flyctl status --app nexus-postgres`
3. Test connection: `flyctl ssh console --app nexus-postgres`
4. Verify network connectivity between apps

### High Latency

1. Check region distribution: `flyctl status --app nexus-bridge-server`
2. Verify edge routing is working
3. Check PostgreSQL replica lag
4. Review Fly.io metrics dashboard

### Out of Memory

1. Increase memory: `flyctl scale memory 1024 --app nexus-bridge-server`
2. Check memory usage: `flyctl status --app nexus-bridge-server`
3. Review application logs for memory leaks

## Maintenance

### Database Migrations

```bash
# Run migrations via Bridge Server
flyctl ssh console --app nexus-bridge-server

# Or use database CLI
cd database-layer-hs
flyctl ssh console --app nexus-postgres
psql $DATABASE_URL -f migrations/001_initial_schema.sql
```

### Backup PostgreSQL

```bash
# Create backup
flyctl postgres backup create --app nexus-postgres

# List backups
flyctl postgres backup list --app nexus-postgres

# Restore backup
flyctl postgres backup restore <backup-id> --app nexus-postgres
```

### Update Dependencies

```bash
# Update Bridge Server
cd bridge-server-ps
# Update dependencies in package.json or spago.dhall
flyctl deploy --app nexus-bridge-server

# Update agent orchestrator
cd ../agent-orchestrator-edge-hs
# Update dependencies in .cabal
flyctl deploy --app nexus-bridge-server
```

## Security

### Network Security

- All traffic uses TLS (HTTPS)
- PostgreSQL uses SCRAM-SHA-256 authentication
- Internal network isolation via Fly.io private networking

### Secrets Security

- Never commit secrets to version control
- Use Fly.io secrets management
- Rotate secrets regularly
- Use different passwords per environment

### Access Control

- Limit Fly.io organization access
- Use SSH keys for console access
- Enable audit logging
- Monitor for suspicious activity

## Cost Optimization

### Right-Sizing

```bash
# Reduce CPU/memory if underutilized
flyctl scale vm shared-cpu-1x --memory 256 --app nexus-bridge-server

# Use shared CPU for non-critical workloads
flyctl scale vm shared-cpu-1x --app nexus-bridge-server
```

### Auto-Stop

Auto-stop is enabled in `fly.toml`:

```toml
auto_stop_machines = true
auto_start_machines = true
min_machines_running = 1
```

This stops unused machines to save costs.

## Support

For issues:
1. Check Fly.io status: https://status.fly.io
2. Review Fly.io docs: https://fly.io/docs
3. Check application logs: `flyctl logs --app nexus-bridge-server`
4. Contact Fly.io support: https://fly.io/support

## Next Steps

After deployment:
1. Run load tests: `./load-test.sh`
2. Monitor metrics in Fly.io dashboard
3. Set up alerts for critical metrics
4. Configure CI/CD for automated deployments
5. Document region-specific configurations
