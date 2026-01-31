#!/bin/bash
# Nexus Multi-Region Deployment Script
# Deploys Bridge Server and PostgreSQL cluster to Fly.io

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Configuration
BRIDGE_APP="nexus-bridge-server"
POSTGRES_APP="nexus-postgres"
REGIONS=("iad" "lhr" "nrt" "sjc")  # Washington, London, Tokyo, San Jose

# Functions
log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

check_prerequisites() {
    log_info "Checking prerequisites..."
    
    if ! command -v flyctl &> /dev/null; then
        log_error "flyctl not found. Install from https://fly.io/docs/hands-on/install-flyctl/"
        exit 1
    fi
    
    if ! flyctl auth whoami &> /dev/null; then
        log_error "Not authenticated with Fly.io. Run: flyctl auth login"
        exit 1
    fi
    
    log_info "Prerequisites check passed"
}

create_postgres_cluster() {
    log_info "Creating PostgreSQL cluster..."
    
    # Check if PostgreSQL app already exists
    if flyctl apps list | grep -q "$POSTGRES_APP"; then
        log_warn "PostgreSQL app '$POSTGRES_APP' already exists. Skipping creation."
    else
        flyctl apps create "$POSTGRES_APP" --org personal || true
    fi
    
    # Deploy PostgreSQL to primary region
    log_info "Deploying PostgreSQL to primary region (iad)..."
    cd "$(dirname "$0")"
    flyctl deploy --config fly.postgres.toml --app "$POSTGRES_APP" --region iad || true
    
    # Create volume for persistent data
    log_info "Creating PostgreSQL volume..."
    flyctl volumes create nexus_postgres_data --app "$POSTGRES_APP" --region iad --size 10 || true
    
    # Set PostgreSQL password secret
    if [ -z "${POSTGRES_PASSWORD:-}" ]; then
        log_warn "POSTGRES_PASSWORD not set. Generating random password..."
        POSTGRES_PASSWORD=$(openssl rand -base64 32)
    fi
    
    flyctl secrets set "POSTGRES_PASSWORD=$POSTGRES_PASSWORD" --app "$POSTGRES_APP" || true
    
    log_info "PostgreSQL cluster created. Waiting for initialization..."
    sleep 10
    
    # Get database URL
    DATABASE_URL=$(flyctl config show --app "$POSTGRES_APP" | grep DATABASE_URL || echo "")
    if [ -z "$DATABASE_URL" ]; then
        # Construct DATABASE_URL from secrets
        POSTGRES_USER="nexus"
        POSTGRES_DB="nexus"
        POSTGRES_HOST=$(flyctl status --app "$POSTGRES_APP" | grep "Hostname" | awk '{print $2}' || echo "$POSTGRES_APP.internal")
        DATABASE_URL="postgresql://$POSTGRES_USER:$POSTGRES_PASSWORD@$POSTGRES_HOST:5432/$POSTGRES_DB?sslmode=require"
    fi
    
    log_info "PostgreSQL cluster ready"
    echo "DATABASE_URL=$DATABASE_URL"
}

create_bridge_server_app() {
    log_info "Creating Bridge Server app..."
    
    # Check if Bridge Server app already exists
    if flyctl apps list | grep -q "$BRIDGE_APP"; then
        log_warn "Bridge Server app '$BRIDGE_APP' already exists. Skipping creation."
    else
        flyctl apps create "$BRIDGE_APP" --org personal || true
    fi
    
    log_info "Bridge Server app created"
}

deploy_bridge_server() {
    log_info "Deploying Bridge Server..."
    
    cd "$(dirname "$0")/bridge-server-ps"
    
    # Build and deploy to primary region first
    log_info "Deploying to primary region (iad)..."
    flyctl deploy --config ../fly.toml --app "$BRIDGE_APP" --region iad
    
    # Deploy to additional regions
    for region in "${REGIONS[@]}"; do
        if [ "$region" != "iad" ]; then
            log_info "Deploying to region: $region"
            flyctl deploy --config ../fly.toml --app "$BRIDGE_APP" --region "$region" || true
        fi
    done
    
    log_info "Bridge Server deployed to all regions"
}

configure_secrets() {
    log_info "Configuring secrets..."
    
    # Set DATABASE_URL for Bridge Server
    if [ -n "${DATABASE_URL:-}" ]; then
        flyctl secrets set "DATABASE_URL=$DATABASE_URL" --app "$BRIDGE_APP" || true
    else
        log_warn "DATABASE_URL not set. Please set it manually:"
        log_warn "flyctl secrets set DATABASE_URL=<url> --app $BRIDGE_APP"
    fi
    
    # Set FLY_API_TOKEN if provided
    if [ -n "${FLY_API_TOKEN:-}" ]; then
        flyctl secrets set "FLY_API_TOKEN=$FLY_API_TOKEN" --app "$BRIDGE_APP" || true
    else
        log_warn "FLY_API_TOKEN not set. Please set it manually:"
        log_warn "flyctl secrets set FLY_API_TOKEN=<token> --app $BRIDGE_APP"
    fi
    
    # Set REGION environment variable for each machine
    for region in "${REGIONS[@]}"; do
        flyctl secrets set "REGION=$region" --app "$BRIDGE_APP" --region "$region" || true
    done
    
    log_info "Secrets configured"
}

setup_health_checks() {
    log_info "Setting up health checks..."
    
    # Health check endpoint should be available at /health
    # This is configured in fly.toml
    
    log_info "Health checks configured"
}

scale_instances() {
    log_info "Scaling instances..."
    
    # Scale Bridge Server to 1 instance per region
    for region in "${REGIONS[@]}"; do
        flyctl scale count 1 --app "$BRIDGE_APP" --region "$region" || true
    done
    
    log_info "Scaling complete"
}

verify_deployment() {
    log_info "Verifying deployment..."
    
    # Check Bridge Server status
    log_info "Bridge Server status:"
    flyctl status --app "$BRIDGE_APP"
    
    # Check PostgreSQL status
    log_info "PostgreSQL status:"
    flyctl status --app "$POSTGRES_APP"
    
    # Test health endpoint
    BRIDGE_URL=$(flyctl status --app "$BRIDGE_APP" | grep "Hostname" | awk '{print "https://" $2 ".fly.dev"}' | head -1)
    if [ -n "$BRIDGE_URL" ]; then
        log_info "Testing health endpoint: $BRIDGE_URL/health"
        curl -f "$BRIDGE_URL/health" || log_warn "Health check failed"
    fi
    
    log_info "Verification complete"
}

# Main deployment flow
main() {
    log_info "Starting Nexus deployment to Fly.io"
    
    check_prerequisites
    create_postgres_cluster
    create_bridge_server_app
    configure_secrets
    deploy_bridge_server
    setup_health_checks
    scale_instances
    verify_deployment
    
    log_info "Deployment complete!"
    log_info "Bridge Server: https://$BRIDGE_APP.fly.dev"
    log_info "PostgreSQL: $POSTGRES_APP.internal"
}

# Run main function
main "$@"
