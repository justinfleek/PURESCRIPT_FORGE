# OpenCode SDK

Type-safe SDK for OpenCode API, generated from PureScript.

## Installation

```bash
npm install @opencode-ai/sdk
```

## Usage

### Basic Client

```typescript
import { createOpencodeClient } from "@opencode-ai/sdk";

const client = createOpencodeClient({
  baseUrl: "http://localhost:4096",
});

// Use the client
const sessions = await client.session.list();
```

### Client + Server

```typescript
import { createOpencode } from "@opencode-ai/sdk";

const { client, server } = await createOpencode({
  hostname: "127.0.0.1",
  port: 4096,
});

// Use client
const health = await client.global.health();

// Close server when done
server.close();
```

## Development

### Building

```bash
npm run build
```

### Type Checking

```bash
npm run typecheck
```

## Architecture

This SDK is generated from PureScript source code:

1. **PureScript Source** (`COMPASS/src/opencode/sdk/`)
   - Type-safe API client
   - Server management
   - Generated types from OpenAPI spec

2. **Codegen Pipeline**
   - PureScript → JavaScript compilation
   - TypeScript definition generation
   - NPM package generation

3. **Distribution**
   - Compiled JavaScript in `dist/`
   - TypeScript definitions
   - NPM package ready for publishing

## Phase 4 Status

- ✅ SDK package structure created
- ✅ Client and Server modules migrated to PureScript
- ✅ Codegen pipeline foundation
- ⏳ Full type generation from OpenAPI
- ⏳ Complete JS/TS codegen
- ⏳ NPM distribution setup
