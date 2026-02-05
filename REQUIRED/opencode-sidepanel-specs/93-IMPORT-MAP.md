# 93-IMPORT-MAP: Complete Module Import Definitions

## Overview

This specification defines every import statement for every module in the codebase, ensuring no circular dependencies and clear module boundaries.

---

## Bridge Server (TypeScript)

### Entry Point

```typescript
// bridge/src/index.ts
import { config } from './config';
import { initDatabase } from './db';
import { createVeniceClient } from './venice';
import { createWebSocketServer } from './websocket';
import { createHttpServer } from './server';
import { logger } from './logging';
```

### Configuration

```typescript
// bridge/src/config.ts
import { z } from 'zod';
import dotenv from 'dotenv';
// NO internal imports - leaf module
```

### Logging

```typescript
// bridge/src/logging/index.ts
import pino from 'pino';
import { config } from '../config';
// NO other internal imports - near-leaf module
```

### Database Layer

```typescript
// bridge/src/db/index.ts
import Database from 'better-sqlite3';
import { config } from '../config';
import { logger } from '../logging';
import { schema } from './schema';
import * as migrations from './migrations';
export { queries } from './queries';

// bridge/src/db/schema.ts
// NO imports - pure type definitions

// bridge/src/db/migrations/index.ts
import { Migration } from './types';
import { v001_initial } from './001_initial';
import { v002_branching } from './002_branching';
import { v003_analytics } from './003_analytics';

// bridge/src/db/queries/sessions.ts
import type { Database } from 'better-sqlite3';
import type { Session, CreateSessionParams } from '../schema';

// bridge/src/db/queries/messages.ts
import type { Database } from 'better-sqlite3';
import type { Message, CreateMessageParams } from '../schema';

// bridge/src/db/queries/balance.ts
import type { Database } from 'better-sqlite3';
import type { BalanceSnapshot } from '../schema';

// bridge/src/db/queries/index.ts
export * from './sessions';
export * from './messages';
export * from './balance';
```

### Venice API Client

```typescript
// bridge/src/venice/index.ts
import { VeniceClient } from './client';
import { ResponseParser } from './parser';
import { VeniceError } from './errors';
export { createVeniceClient } from './client';

// bridge/src/venice/client.ts
import { config } from '../config';
import { logger } from '../logging';
import { VeniceError, ErrorCode } from './errors';
import { parseResponse, parseBalance } from './parser';
import type { ChatRequest, ChatResponse, Balance } from './types';

// bridge/src/venice/parser.ts
import type { 
  ChatResponse, 
  Balance, 
  VeniceHeaders,
  StreamChunk 
} from './types';
// NO other internal imports

// bridge/src/venice/errors.ts
// NO imports - pure definitions

// bridge/src/venice/types.ts
// NO imports - pure type definitions
```

### WebSocket Server

```typescript
// bridge/src/websocket/index.ts
import { WebSocketServer } from 'ws';
import { config } from '../config';
import { logger } from '../logging';
import { Protocol } from './protocol';
import { createHandlers } from './handlers';
export { createWebSocketServer };

// bridge/src/websocket/protocol.ts
import type { JsonRpcRequest, JsonRpcResponse } from '../../shared/types/jsonrpc';
// NO other imports - protocol definitions

// bridge/src/websocket/handlers/index.ts
import { sessionHandlers } from './session';
import { balanceHandlers } from './balance';
import { stateHandlers } from './state';
export const createHandlers = (deps: HandlerDeps) => ({
  ...sessionHandlers(deps),
  ...balanceHandlers(deps),
  ...stateHandlers(deps)
});

// bridge/src/websocket/handlers/session.ts
import type { HandlerDeps } from '../types';
import { queries } from '../../db';
import type { Session, CreateSessionParams } from '../../db/schema';

// bridge/src/websocket/handlers/balance.ts
import type { HandlerDeps } from '../types';
import type { Balance } from '../../venice/types';

// bridge/src/websocket/handlers/state.ts
import type { HandlerDeps } from '../types';
import { queries } from '../../db';
```

### HTTP Server

```typescript
// bridge/src/server.ts
import express from 'express';
import cors from 'cors';
import { config } from './config';
import { logger } from './logging';
import { healthRoutes } from './routes/health';
import { metricsRoutes } from './routes/metrics';

// bridge/src/routes/health.ts
import { Router } from 'express';
import type { Database } from 'better-sqlite3';
import type { VeniceClient } from '../venice';

// bridge/src/routes/metrics.ts
import { Router } from 'express';
import { Registry } from 'prom-client';
```

---

## Shared Types

```typescript
// shared/types/index.ts
export * from './jsonrpc';
export * from './session';
export * from './balance';
export * from './message';
export * from './events';

// shared/types/jsonrpc.ts
// NO imports - base protocol types

// shared/types/session.ts
import type { Message } from './message';

// shared/types/balance.ts
// NO imports - pure types

// shared/types/message.ts
// NO imports - pure types

// shared/types/events.ts
import type { Session } from './session';
import type { Balance } from './balance';
import type { Message } from './message';
```

---

## Frontend (PureScript)

### Entry Point

```purescript
-- frontend/src/Main.purs
module Main where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_)
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)

import App.Router (component) as Router
import App.Store (createStore)
import App.WebSocket (connect) as WebSocket
```

### App Core

```purescript
-- frontend/src/App/Router.purs
module App.Router where

import Prelude

import Data.Maybe (Maybe(..))
import Halogen as H
import Halogen.HTML as HH
import Routing.Hash (matches)

import App.State (AppState)
import App.Store (Store)
import Pages.Home (component) as Home
import Pages.Session (component) as Session
import Pages.Settings (component) as Settings
import Types.Route (Route(..))

-- frontend/src/App/Store.purs
module App.Store where

import Prelude

import Effect.Ref (Ref)
import Effect.Ref as Ref

import App.State (AppState, initialState)
import Types.Action (Action)

-- frontend/src/App/State.purs
module App.State where

import Prelude

import Data.Map (Map)
import Data.Map as Map

import Types.Session (Session, SessionId)
import Types.Balance (Balance)
import Types.Connection (ConnectionState)

-- frontend/src/App/WebSocket.purs
module App.WebSocket where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)

import App.State (AppState)
import FFI.WebSocket (WebSocket)
import Types.Protocol (JsonRpcMessage)
```

### Types

```purescript
-- frontend/src/Types/Session.purs
module Types.Session where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)

-- NO internal imports - pure types

-- frontend/src/Types/Balance.purs
module Types.Balance where

import Prelude

import Data.DateTime (DateTime)

-- NO internal imports - pure types

-- frontend/src/Types/Message.purs
module Types.Message where

import Prelude

import Data.DateTime (DateTime)
import Types.Session (SessionId)

-- frontend/src/Types/Connection.purs
module Types.Connection where

import Prelude

-- NO internal imports - pure types

-- frontend/src/Types/Protocol.purs
module Types.Protocol where

import Prelude

import Data.Argonaut (Json)
import Data.Maybe (Maybe)

import Types.Session (Session)
import Types.Balance (Balance)
import Types.Message (Message)

-- frontend/src/Types/Route.purs
module Types.Route where

import Prelude

import Types.Session (SessionId)

-- frontend/src/Types/Action.purs
module Types.Action where

import Prelude

import Types.Session (Session, SessionId)
import Types.Balance (Balance)
import Types.Message (Message)
import Types.Connection (ConnectionState)
```

### Components

```purescript
-- frontend/src/Component/Dashboard.purs
module Component.Dashboard where

import Prelude

import Halogen as H
import Halogen.HTML as HH

import App.State (AppState)
import Component.DiemWidget (diemWidget)
import Component.Countdown (countdown)
import Component.TokenChart (tokenChart)
import Component.SessionList (sessionList)

-- frontend/src/Component/DiemWidget.purs
module Component.DiemWidget where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

import Types.Balance (Balance, DiemStatus)
import FFI.Recharts (sparkline)

-- frontend/src/Component/Countdown.purs
module Component.Countdown where

import Prelude

import Effect.Timer (setInterval, clearInterval)
import Halogen as H

import Types.Balance (secondsToMidnight)

-- frontend/src/Component/SessionPanel.purs
module Component.SessionPanel where

import Prelude

import Data.Array as Array
import Halogen as H
import Halogen.HTML as HH

import App.State (AppState)
import Types.Session (Session, SessionId)
import Types.Message (Message)
import Component.MessageList (messageList)
import Component.FileContext (fileContext)

-- frontend/src/Component/TokenChart.purs
module Component.TokenChart where

import Prelude

import Halogen as H

import Types.Balance (TokenUsage)
import FFI.Recharts (lineChart, areaChart)

-- frontend/src/Component/MessageList.purs
module Component.MessageList where

import Prelude

import Halogen as H
import Halogen.HTML as HH

import Types.Message (Message)

-- frontend/src/Component/FileContext.purs
module Component.FileContext where

import Prelude

import Halogen as H
import Halogen.HTML as HH

import Types.Session (FileContext)

-- frontend/src/Component/SessionList.purs
module Component.SessionList where

import Prelude

import Data.Array as Array
import Halogen as H
import Halogen.HTML as HH

import Types.Session (Session)

-- frontend/src/Component/CommandPalette.purs
module Component.CommandPalette where

import Prelude

import Data.Foldable (find)
import Halogen as H
import Halogen.HTML as HH

import Types.Action (Action)
import Component.KeyboardShortcut (useKeyboard)
```

### Pages

```purescript
-- frontend/src/Pages/Home.purs
module Pages.Home where

import Prelude

import Halogen as H

import App.State (AppState)
import Component.Dashboard (dashboard)

-- frontend/src/Pages/Session.purs
module Pages.Session where

import Prelude

import Halogen as H

import App.State (AppState)
import Types.Session (SessionId)
import Component.SessionPanel (sessionPanel)

-- frontend/src/Pages/Settings.purs
module Pages.Settings where

import Prelude

import Halogen as H

import App.State (AppState)
import Component.Settings (settings)
```

### FFI Bindings

```purescript
-- frontend/src/FFI/WebSocket.purs
module FFI.WebSocket where

import Prelude

import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2)
import Data.Function.Uncurried (Fn2)

foreign import data WebSocket :: Type
foreign import connect :: String -> Effect WebSocket
foreign import send :: WebSocket -> String -> Effect Unit
foreign import close :: WebSocket -> Effect Unit
foreign import onMessage :: WebSocket -> (String -> Effect Unit) -> Effect Unit

-- frontend/src/FFI/Recharts.purs
module FFI.Recharts where

import Prelude

import Halogen.HTML as HH
import React.Basic (JSX)

foreign import lineChart :: forall r. { | r } -> JSX
foreign import areaChart :: forall r. { | r } -> JSX
foreign import sparkline :: forall r. { | r } -> JSX

-- frontend/src/FFI/LocalStorage.purs
module FFI.LocalStorage where

import Prelude

import Effect (Effect)
import Data.Maybe (Maybe)

foreign import getItem :: String -> Effect (Maybe String)
foreign import setItem :: String -> String -> Effect Unit
foreign import removeItem :: String -> Effect Unit
```

---

## Import Dependency Matrix

```
┌───────────────────────────────────────────────────────────────────────────┐
│                        IMPORT DEPENDENCY MATRIX                          │
├───────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  Module              │ Imports From                                       │
│  ────────────────────┼───────────────────────────────────────────────────│
│  config              │ (external only)                                   │
│  logging             │ config                                            │
│  db/schema           │ (none - types only)                               │
│  db/queries          │ schema                                            │
│  db/migrations       │ schema                                            │
│  db/index            │ config, logging, schema, queries, migrations      │
│  venice/types        │ (none - types only)                               │
│  venice/errors       │ (none - types only)                               │
│  venice/parser       │ types                                             │
│  venice/client       │ config, logging, errors, parser, types            │
│  venice/index        │ client, parser, errors                            │
│  websocket/protocol  │ shared/types                                      │
│  websocket/handlers  │ db/queries, venice/types                          │
│  websocket/index     │ config, logging, protocol, handlers               │
│  server              │ config, logging, routes/*                         │
│  routes/health       │ db, venice                                        │
│  routes/metrics      │ (external only)                                   │
│  index (entry)       │ config, db, venice, websocket, server, logging    │
│                                                                           │
└───────────────────────────────────────────────────────────────────────────┘
```

---

## Validation Rules

### No Circular Dependencies

```typescript
// FORBIDDEN patterns:
// ❌ db/queries → websocket/handlers → db/queries
// ❌ venice/client → venice/parser → venice/client
// ❌ Component.A → Component.B → Component.A

// Use madge to verify:
// npx madge --circular bridge/src/
```

### Leaf Modules

```
These modules must have ZERO internal imports:
- config.ts
- db/schema.ts
- venice/types.ts
- venice/errors.ts
- shared/types/*.ts
- Types/*.purs (PureScript)
```

### Layer Boundaries

```
ALLOWED:
  websocket → db (same layer down)
  websocket → venice (same layer cross)
  
FORBIDDEN:
  db → websocket (never up)
  config → anything (leaf only)
```

---

## Related Specifications

- `91-DEPENDENCY-GRAPH.md` - Visual dependency graph
- `07-PROJECT-STRUCTURE.md` - Directory layout
- `40-PURESCRIPT-ARCHITECTURE.md` - Frontend architecture

---

*"Know your imports before you write your code."*
