# Dockerfile for Nexus Bridge Server (PureScript/Node.js)
# Multi-stage build for optimized production image

# Stage 1: Build PureScript
FROM node:20-slim AS purescript-builder

WORKDIR /build

# Install PureScript compiler and Spago
RUN npm install -g purescript@0.15.11 spago@0.21.0

# Copy PureScript source files
COPY spago.dhall ./
COPY src ./src

# Install PureScript dependencies
RUN spago install

# Build PureScript to JavaScript
RUN spago build

# Stage 2: Install Node.js dependencies
FROM node:20-slim AS node-builder

WORKDIR /build

# Copy package.json if it exists, otherwise create one with required dependencies
COPY package*.json ./
RUN if [ ! -f package.json ]; then \
      echo '{"name":"nexus-bridge-server","version":"0.1.0","dependencies":{"ws":"^8.x","express":"^4.x","pg":"^8.x","pino":"^8.x"}}' > package.json; \
    fi

# Install Node.js dependencies
RUN npm ci --production

# Copy PureScript output from previous stage
COPY --from=purescript-builder /build/output ./output

# Copy JavaScript FFI files
COPY src ./src

# Stage 3: Runtime image
FROM node:20-slim

WORKDIR /app

# Install runtime dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Copy built application from builder stage
COPY --from=node-builder /build/output ./output
COPY --from=node-builder /build/src ./src
COPY --from=node-builder /build/node_modules ./node_modules
COPY --from=node-builder /build/package.json ./package.json

# Create entry script that properly loads the PureScript main module
RUN echo '#!/bin/sh\n\
if [ -f "./output/Bridge.Main/index.js" ]; then\n\
  node ./output/Bridge.Main/index.js\n\
elif [ -f "./output/Main/index.js" ]; then\n\
  node ./output/Main/index.js\n\
else\n\
  echo "Error: Could not find PureScript entry point"\n\
  exit 1\n\
fi\n\
' > /app/start.sh && chmod +x /app/start.sh

# Expose port
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
  CMD node -e "require('http').get('http://localhost:8080/health', (r) => { process.exit(r.statusCode === 200 ? 0 : 1) })" || exit 1

# Start server
CMD ["/app/start.sh"]
