# Dockerfile for Nexus Edge Orchestrator (Haskell)
# Multi-stage build for optimized production image

# Stage 1: Build Haskell application
FROM haskell:9.6-slim AS haskell-builder

WORKDIR /build

# Install build dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
    build-essential \
    libpq-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Copy Cabal files
COPY nexus-agent-orchestrator-edge-hs.cabal ./

# Copy source files
COPY app ./app
COPY src ./src

# Install dependencies and build
RUN cabal update && \
    cabal build --dependencies-only && \
    cabal build --enable-executable-dynamic

# Stage 2: Runtime image
FROM debian:bookworm-slim

WORKDIR /app

# Install runtime dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
    libgmp10 \
    libpq5 \
    ca-certificates \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Copy built executable from builder stage
COPY --from=haskell-builder /build/dist-newstyle/build/x86_64-linux/ghc-9.6.*/nexus-agent-orchestrator-edge-hs-0.1.0.0/x/nexus-edge-orchestrator-cli/build/nexus-edge-orchestrator-cli/nexus-edge-orchestrator-cli /app/nexus-edge-orchestrator

# Make executable
RUN chmod +x /app/nexus-edge-orchestrator

# Health check script
RUN echo '#!/bin/sh\n\
  /app/nexus-edge-orchestrator list-regions > /dev/null 2>&1\n\
' > /app/healthcheck.sh && chmod +x /app/healthcheck.sh

# Health check
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
  CMD /app/healthcheck.sh || exit 1

# Default command (can be overridden)
CMD ["/app/nexus-edge-orchestrator"]
