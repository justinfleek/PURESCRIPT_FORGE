# Deployment Configuration - Automated Deployment Pipeline
#
# **What:** Provides Nix-based deployment configuration for Bridge Server and related services.
#         Supports deployment to Fly.io, local development, and production environments.
# **Why:** Enables reproducible deployments with rollback capabilities. Ensures consistent
#         deployment process across environments.
# **How:** Defines deployment derivations, health checks, and rollback procedures.
#
# **Usage:**
# ```bash
# # Deploy to production
# nix run .#deploy -- production
#
# # Deploy to staging
# nix run .#deploy -- staging
#
# # Rollback
# nix run .#rollback -- production <version>
# ```

{ pkgs, lib, bridge-server-ps, bridge-database-hs, ... }:

let
  # Deployment targets
  deploymentTargets = {
    production = {
      flyApp = "nexus-bridge-server";
      region = "iad";
      machineSize = "shared-cpu-1x";
      minMachines = 1;
      healthCheckPath = "/health";
      healthCheckInterval = "10s";
      healthCheckTimeout = "5s";
      healthCheckGracePeriod = "30s";
    };
    
    staging = {
      flyApp = "nexus-bridge-server-staging";
      region = "iad";
      machineSize = "shared-cpu-1x";
      minMachines = 1;
      healthCheckPath = "/health";
      healthCheckInterval = "10s";
      healthCheckTimeout = "5s";
      healthCheckGracePeriod = "30s";
    };
    
    development = {
      flyApp = "nexus-bridge-server-dev";
      region = "iad";
      machineSize = "shared-cpu-1x";
      minMachines = 0;
      healthCheckPath = "/health";
      healthCheckInterval = "10s";
      healthCheckTimeout = "5s";
      healthCheckGracePeriod = "30s";
    };
  };

  # Build deployment package
  buildDeploymentPackage = { target, version ? "latest" }:
    pkgs.stdenv.mkDerivation {
      name = "bridge-server-deployment-${target}-${version}";
      
      buildInputs = with pkgs; [
        bridge-server-ps
        bridge-database-hs
        jq
        curl
      ];
      
      nativeBuildInputs = with pkgs; [
        flyctl
      ];
      
      buildPhase = ''
        echo "Building deployment package for ${target}"
        mkdir -p $out/bin
        mkdir -p $out/config
        mkdir -p $out/scripts
        
        # Copy binaries
        cp ${bridge-server-ps}/bin/* $out/bin/ || true
        cp ${bridge-database-hs}/bin/* $out/bin/ || true
        
        # Generate deployment script
        cat > $out/scripts/deploy.sh << 'DEPLOY_SCRIPT'
        #!/bin/sh
        set -e
        
        TARGET="$1"
        VERSION="$2"
        
        if [ -z "$TARGET" ]; then
          echo "Usage: deploy.sh <target> [version]"
          exit 1
        fi
        
        # Get deployment config
        CONFIG=$(cat $out/config/${TARGET}.json)
        FLY_APP=$(echo "$CONFIG" | jq -r '.flyApp')
        REGION=$(echo "$CONFIG" | jq -r '.region')
        
        echo "Deploying to ${TARGET} (${FLY_APP})..."
        
        # Build Docker image
        echo "Building Docker image..."
        docker build -t ${FLY_APP}:${VERSION} -f $out/Dockerfile .
        
        # Push to Fly.io
        echo "Pushing to Fly.io..."
        flyctl deploy --app "$FLY_APP" --image "${FLY_APP}:${VERSION}" --region "$REGION"
        
        # Wait for health check
        echo "Waiting for health check..."
        sleep 30
        
        # Verify deployment
        HEALTH_URL="https://${FLY_APP}.fly.dev/health"
        if curl -f "$HEALTH_URL" > /dev/null 2>&1; then
          echo "Deployment successful!"
        else
          echo "Health check failed!"
          exit 1
        fi
        DEPLOY_SCRIPT
        
        chmod +x $out/scripts/deploy.sh
        
        # Generate rollback script
        cat > $out/scripts/rollback.sh << 'ROLLBACK_SCRIPT'
        #!/bin/sh
        set -e
        
        TARGET="$1"
        VERSION="$2"
        
        if [ -z "$TARGET" ] || [ -z "$VERSION" ]; then
          echo "Usage: rollback.sh <target> <version>"
          exit 1
        fi
        
        CONFIG=$(cat $out/config/${TARGET}.json)
        FLY_APP=$(echo "$CONFIG" | jq -r '.flyApp')
        
        echo "Rolling back ${FLY_APP} to version ${VERSION}..."
        
        flyctl releases rollback --app "$FLY_APP" "$VERSION"
        
        echo "Rollback complete!"
        ROLLBACK_SCRIPT
        
        chmod +x $out/scripts/rollback.sh
        
        # Generate config files
        mkdir -p $out/config
        for target in production staging development; do
          echo "${builtins.toJSON (builtins.getAttr target deploymentTargets)}" > $out/config/${target}.json
        done
      '';
      
      installPhase = ''
        echo "Deployment package built"
      '';
    };

  # Health check script
  healthCheck = pkgs.writeShellScriptBin "health-check" ''
    #!/bin/sh
    set -e
    
    TARGET="$1"
    HEALTH_URL="$2"
    
    if [ -z "$HEALTH_URL" ]; then
      echo "Usage: health-check <target> <health-url>"
      exit 1
    fi
    
    echo "Checking health at $HEALTH_URL..."
    
    MAX_RETRIES=10
    RETRY_COUNT=0
    
    while [ $RETRY_COUNT -lt $MAX_RETRIES ]; do
      if curl -f "$HEALTH_URL" > /dev/null 2>&1; then
        echo "Health check passed!"
        exit 0
      fi
      
      RETRY_COUNT=$((RETRY_COUNT + 1))
      echo "Health check failed, retrying ($RETRY_COUNT/$MAX_RETRIES)..."
      sleep 5
    done
    
    echo "Health check failed after $MAX_RETRIES attempts"
    exit 1
  '';

  # Deployment verification script
  verifyDeployment = pkgs.writeShellScriptBin "verify-deployment" ''
    #!/bin/sh
    set -e
    
    TARGET="$1"
    
    if [ -z "$TARGET" ]; then
      echo "Usage: verify-deployment <target>"
      exit 1
    fi
    
    CONFIG=$(cat ${buildDeploymentPackage { target = TARGET; }}/config/${TARGET}.json)
    FLY_APP=$(echo "$CONFIG" | jq -r '.flyApp')
    HEALTH_PATH=$(echo "$CONFIG" | jq -r '.healthCheckPath')
    
    HEALTH_URL="https://${FLY_APP}.fly.dev${HEALTH_PATH}"
    
    echo "Verifying deployment for ${TARGET}..."
    echo "Health URL: $HEALTH_URL"
    
    # Check health endpoint
    ${healthCheck}/bin/health-check "$TARGET" "$HEALTH_URL"
    
    # Check metrics endpoint
    METRICS_URL="https://${FLY_APP}.fly.dev/metrics"
    if curl -f "$METRICS_URL" > /dev/null 2>&1; then
      echo "Metrics endpoint accessible"
    else
      echo "Warning: Metrics endpoint not accessible"
    fi
    
    echo "Deployment verification complete!"
  '';

in
{
  # Deployment packages
  deploy-production = buildDeploymentPackage { target = "production"; };
  deploy-staging = buildDeploymentPackage { target = "staging"; };
  deploy-development = buildDeploymentPackage { target = "development"; };
  
  # Deployment scripts
  deploy = pkgs.writeShellScriptBin "deploy" ''
    #!/bin/sh
    set -e
    
    TARGET="$1"
    
    if [ -z "$TARGET" ]; then
      echo "Usage: deploy <target>"
      echo "Targets: production, staging, development"
      exit 1
    fi
    
    case "$TARGET" in
      production)
        DEPLOY_PKG=${buildDeploymentPackage { target = "production"; }}
        ;;
      staging)
        DEPLOY_PKG=${buildDeploymentPackage { target = "staging"; }}
        ;;
      development)
        DEPLOY_PKG=${buildDeploymentPackage { target = "development"; }}
        ;;
      *)
        echo "Invalid target: $TARGET"
        exit 1
        ;;
    esac
    
    VERSION=$(date +%Y%m%d-%H%M%S)
    
    echo "Deploying to $TARGET (version: $VERSION)..."
    $DEPLOY_PKG/scripts/deploy.sh "$TARGET" "$VERSION"
  '';
  
  rollback = pkgs.writeShellScriptBin "rollback" ''
    #!/bin/sh
    set -e
    
    TARGET="$1"
    VERSION="$2"
    
    if [ -z "$TARGET" ] || [ -z "$VERSION" ]; then
      echo "Usage: rollback <target> <version>"
      echo "Targets: production, staging, development"
      exit 1
    fi
    
    case "$TARGET" in
      production)
        DEPLOY_PKG=${buildDeploymentPackage { target = "production"; }}
        ;;
      staging)
        DEPLOY_PKG=${buildDeploymentPackage { target = "staging"; }}
        ;;
      development)
        DEPLOY_PKG=${buildDeploymentPackage { target = "development"; }}
        ;;
      *)
        echo "Invalid target: $TARGET"
        exit 1
        ;;
    esac
    
    echo "Rolling back $TARGET to version $VERSION..."
    $DEPLOY_PKG/scripts/rollback.sh "$TARGET" "$VERSION"
  '';
  
  # Health check and verification
  inherit healthCheck verifyDeployment;
}
