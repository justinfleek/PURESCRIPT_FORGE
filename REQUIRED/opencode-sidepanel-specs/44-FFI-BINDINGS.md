# 44-FFI-BINDINGS: JavaScript Interoperability

## Overview

This document defines patterns for PureScript Foreign Function Interface (FFI) bindings to JavaScript libraries used in the sidepanel: xterm.js, Recharts, WebSocket, localStorage, and browser APIs.

---

## FFI Principles

1. **Type safety at the boundary** - Wrap all JS in typed PureScript functions
2. **Effect marking** - All side effects wrapped in Effect/Aff
3. **Null handling** - Convert nullable JS to Maybe
4. **Error handling** - Catch JS exceptions, convert to Either

---

## Project Structure

```
frontend/src/
├── Sidepanel/
│   └── FFI/
│       ├── Terminal.purs      # xterm.js bindings
│       ├── Terminal.js
│       ├── Charts.purs        # Recharts bindings
│       ├── Charts.js
│       ├── WebSocket.purs     # WebSocket bindings
│       ├── WebSocket.js
│       ├── Storage.purs       # localStorage bindings
│       ├── Storage.js
│       ├── Clipboard.purs     # Clipboard API
│       ├── Clipboard.js
│       ├── DateTime.purs      # Date/time utilities
│       └── DateTime.js
```

---

## WebSocket FFI

### PureScript Types

```purescript
-- frontend/src/Sidepanel/FFI/WebSocket.purs
module Sidepanel.FFI.WebSocket where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- Opaque WebSocket type
foreign import data WebSocketConnection :: Type

-- Connection state
data ReadyState
  = Connecting  -- 0
  | Open        -- 1
  | Closing     -- 2
  | Closed      -- 3

-- Events
type MessageHandler = String -> Effect Unit
type OpenHandler = Effect Unit
type CloseHandler = { code :: Int, reason :: String } -> Effect Unit
type ErrorHandler = String -> Effect Unit

-- Create and connect
foreign import connect :: String -> Effect WebSocketConnection

-- Send message
foreign import send :: WebSocketConnection -> String -> Effect (Either String Unit)

-- Close connection
foreign import close :: WebSocketConnection -> Effect Unit
foreign import closeWithCode :: WebSocketConnection -> Int -> String -> Effect Unit

-- Get state
foreign import getReadyState :: WebSocketConnection -> Effect ReadyState

-- Event handlers
foreign import onMessage :: WebSocketConnection -> MessageHandler -> Effect Unit
foreign import onOpen :: WebSocketConnection -> OpenHandler -> Effect Unit
foreign import onClose :: WebSocketConnection -> CloseHandler -> Effect Unit
foreign import onError :: WebSocketConnection -> ErrorHandler -> Effect Unit

-- Remove handlers
foreign import removeMessageHandler :: WebSocketConnection -> Effect Unit
foreign import removeAllHandlers :: WebSocketConnection -> Effect Unit
```

### JavaScript Implementation

```javascript
// frontend/src/Sidepanel/FFI/WebSocket.js

export function connect(url) {
  return function() {
    return new WebSocket(url);
  };
}

export function send(ws) {
  return function(message) {
    return function() {
      try {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(message);
          return { tag: 'Right', value: {} };
        } else {
          return { tag: 'Left', value: 'WebSocket not open' };
        }
      } catch (e) {
        return { tag: 'Left', value: e.message };
      }
    };
  };
}

export function close(ws) {
  return function() {
    ws.close();
  };
}

export function closeWithCode(ws) {
  return function(code) {
    return function(reason) {
      return function() {
        ws.close(code, reason);
      };
    };
  };
}

export function getReadyState(ws) {
  return function() {
    switch (ws.readyState) {
      case 0: return { tag: 'Connecting' };
      case 1: return { tag: 'Open' };
      case 2: return { tag: 'Closing' };
      case 3: return { tag: 'Closed' };
      default: return { tag: 'Closed' };
    }
  };
}

export function onMessage(ws) {
  return function(handler) {
    return function() {
      ws._messageHandler = function(event) {
        handler(event.data)();
      };
      ws.addEventListener('message', ws._messageHandler);
    };
  };
}

export function onOpen(ws) {
  return function(handler) {
    return function() {
      ws._openHandler = function() {
        handler();
      };
      ws.addEventListener('open', ws._openHandler);
    };
  };
}

export function onClose(ws) {
  return function(handler) {
    return function() {
      ws._closeHandler = function(event) {
        handler({ code: event.code, reason: event.reason })();
      };
      ws.addEventListener('close', ws._closeHandler);
    };
  };
}

export function onError(ws) {
  return function(handler) {
    return function() {
      ws._errorHandler = function(event) {
        handler(event.message || 'Unknown error')();
      };
      ws.addEventListener('error', ws._errorHandler);
    };
  };
}

export function removeMessageHandler(ws) {
  return function() {
    if (ws._messageHandler) {
      ws.removeEventListener('message', ws._messageHandler);
      delete ws._messageHandler;
    }
  };
}

export function removeAllHandlers(ws) {
  return function() {
    if (ws._messageHandler) ws.removeEventListener('message', ws._messageHandler);
    if (ws._openHandler) ws.removeEventListener('open', ws._openHandler);
    if (ws._closeHandler) ws.removeEventListener('close', ws._closeHandler);
    if (ws._errorHandler) ws.removeEventListener('error', ws._errorHandler);
  };
}
```

---

## Recharts FFI

### PureScript Types

```purescript
-- frontend/src/Sidepanel/FFI/Charts.purs
module Sidepanel.FFI.Charts where

import Prelude
import Effect (Effect)
import Web.HTML.HTMLElement (HTMLElement)
import Foreign (Foreign)
import Data.Array (Array)

-- Chart configuration
type LineChartConfig =
  { width :: Int
  , height :: Int
  , data :: Array ChartDataPoint
  , xAxisKey :: String
  , lines :: Array LineConfig
  , showGrid :: Boolean
  , showTooltip :: Boolean
  , showLegend :: Boolean
  }

type ChartDataPoint = 
  { timestamp :: String
  , value1 :: Number
  , value2 :: Number
  }

type LineConfig =
  { dataKey :: String
  , stroke :: String
  , strokeWidth :: Int
  , name :: String
  , dot :: Boolean
  }

type AreaChartConfig =
  { width :: Int
  , height :: Int
  , data :: Array ChartDataPoint
  , xAxisKey :: String
  , areas :: Array AreaConfig
  }

type AreaConfig =
  { dataKey :: String
  , fill :: String
  , stroke :: String
  , fillOpacity :: Number
  }

type PieChartConfig =
  { width :: Int
  , height :: Int
  , data :: Array PieDataPoint
  , innerRadius :: Int
  , outerRadius :: Int
  , showLabels :: Boolean
  }

type PieDataPoint =
  { name :: String
  , value :: Number
  , color :: String
  }

-- Render functions
foreign import renderLineChart :: HTMLElement -> LineChartConfig -> Effect Unit
foreign import renderAreaChart :: HTMLElement -> AreaChartConfig -> Effect Unit
foreign import renderPieChart :: HTMLElement -> PieChartConfig -> Effect Unit

-- Update data (without full re-render)
foreign import updateChartData :: HTMLElement -> Array ChartDataPoint -> Effect Unit

-- Cleanup
foreign import destroyChart :: HTMLElement -> Effect Unit
```

### JavaScript Implementation

```javascript
// frontend/src/Sidepanel/FFI/Charts.js
import React from 'react';
import { createRoot } from 'react-dom/client';
import {
  LineChart, Line, AreaChart, Area, PieChart, Pie,
  XAxis, YAxis, CartesianGrid, Tooltip, Legend,
  ResponsiveContainer, Cell
} from 'recharts';

// Store roots for cleanup
const chartRoots = new WeakMap();

export function renderLineChart(container) {
  return function(config) {
    return function() {
      // Create or get root
      let root = chartRoots.get(container);
      if (!root) {
        root = createRoot(container);
        chartRoots.set(container, root);
      }
      
      const element = React.createElement(
        ResponsiveContainer,
        { width: '100%', height: config.height },
        React.createElement(
          LineChart,
          { data: config.data },
          config.showGrid && React.createElement(CartesianGrid, { strokeDasharray: '3 3', stroke: '#27272a' }),
          React.createElement(XAxis, { 
            dataKey: config.xAxisKey,
            stroke: '#71717a',
            fontSize: 11,
            tickFormatter: formatTime
          }),
          React.createElement(YAxis, { 
            stroke: '#71717a',
            fontSize: 11,
            tickFormatter: formatNumber
          }),
          config.showTooltip && React.createElement(Tooltip, {
            contentStyle: {
              backgroundColor: '#18181b',
              border: '1px solid #27272a',
              borderRadius: '4px',
              fontSize: '12px'
            }
          }),
          config.showLegend && React.createElement(Legend, {
            wrapperStyle: { fontSize: '12px' }
          }),
          ...config.lines.map(line =>
            React.createElement(Line, {
              key: line.dataKey,
              type: 'monotone',
              dataKey: line.dataKey,
              stroke: line.stroke,
              strokeWidth: line.strokeWidth,
              name: line.name,
              dot: line.dot
            })
          )
        )
      );
      
      root.render(element);
    };
  };
}

export function renderAreaChart(container) {
  return function(config) {
    return function() {
      let root = chartRoots.get(container);
      if (!root) {
        root = createRoot(container);
        chartRoots.set(container, root);
      }
      
      const element = React.createElement(
        ResponsiveContainer,
        { width: '100%', height: config.height },
        React.createElement(
          AreaChart,
          { data: config.data },
          React.createElement(CartesianGrid, { strokeDasharray: '3 3', stroke: '#27272a' }),
          React.createElement(XAxis, { dataKey: config.xAxisKey, stroke: '#71717a' }),
          React.createElement(YAxis, { stroke: '#71717a' }),
          React.createElement(Tooltip),
          ...config.areas.map(area =>
            React.createElement(Area, {
              key: area.dataKey,
              type: 'monotone',
              dataKey: area.dataKey,
              fill: area.fill,
              stroke: area.stroke,
              fillOpacity: area.fillOpacity
            })
          )
        )
      );
      
      root.render(element);
    };
  };
}

export function renderPieChart(container) {
  return function(config) {
    return function() {
      let root = chartRoots.get(container);
      if (!root) {
        root = createRoot(container);
        chartRoots.set(container, root);
      }
      
      const element = React.createElement(
        ResponsiveContainer,
        { width: '100%', height: config.height },
        React.createElement(
          PieChart,
          {},
          React.createElement(
            Pie,
            {
              data: config.data,
              dataKey: 'value',
              nameKey: 'name',
              cx: '50%',
              cy: '50%',
              innerRadius: config.innerRadius,
              outerRadius: config.outerRadius,
              label: config.showLabels
            },
            config.data.map((entry, index) =>
              React.createElement(Cell, { key: index, fill: entry.color })
            )
          ),
          React.createElement(Tooltip),
          React.createElement(Legend)
        )
      );
      
      root.render(element);
    };
  };
}

export function updateChartData(container) {
  return function(newData) {
    return function() {
      // This would need to store config and re-render
      // For now, full re-render is the pattern
      console.warn('updateChartData: use full re-render');
    };
  };
}

export function destroyChart(container) {
  return function() {
    const root = chartRoots.get(container);
    if (root) {
      root.unmount();
      chartRoots.delete(container);
    }
  };
}

function formatTime(timestamp) {
  const date = new Date(timestamp);
  return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
}

function formatNumber(num) {
  if (num >= 1000) {
    return (num / 1000).toFixed(1) + 'k';
  }
  return num.toString();
}
```

---

## LocalStorage FFI

```purescript
-- frontend/src/Sidepanel/FFI/Storage.purs
module Sidepanel.FFI.Storage where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Data.Either (Either)
import Data.Argonaut (class DecodeJson, class EncodeJson, decodeJson, encodeJson, stringify, parseJson)

-- Raw storage operations
foreign import getItemRaw :: String -> Effect (Maybe String)
foreign import setItemRaw :: String -> String -> Effect Unit
foreign import removeItemRaw :: String -> Effect Unit
foreign import clearRaw :: Effect Unit
foreign import keysRaw :: Effect (Array String)

-- Typed wrappers
getItem :: forall a. DecodeJson a => String -> Effect (Maybe a)
getItem key = do
  mStr <- getItemRaw key
  pure $ mStr >>= (parseJson >=> decodeJson >>> hush)

setItem :: forall a. EncodeJson a => String -> a -> Effect Unit
setItem key value = setItemRaw key (stringify $ encodeJson value)

removeItem :: String -> Effect Unit
removeItem = removeItemRaw

clear :: Effect Unit
clear = clearRaw

keys :: Effect (Array String)
keys = keysRaw
```

```javascript
// frontend/src/Sidepanel/FFI/Storage.js

export function getItemRaw(key) {
  return function() {
    const value = localStorage.getItem(key);
    if (value === null) {
      return { tag: 'Nothing' };
    }
    return { tag: 'Just', value: value };
  };
}

export function setItemRaw(key) {
  return function(value) {
    return function() {
      localStorage.setItem(key, value);
    };
  };
}

export function removeItemRaw(key) {
  return function() {
    localStorage.removeItem(key);
  };
}

export function clearRaw() {
  localStorage.clear();
}

export function keysRaw() {
  return Object.keys(localStorage);
}
```

---

## DateTime FFI

```purescript
-- frontend/src/Sidepanel/FFI/DateTime.purs
module Sidepanel.FFI.DateTime where

import Prelude
import Effect (Effect)

-- Current time
foreign import now :: Effect Number  -- Unix timestamp ms
foreign import nowISO :: Effect String  -- ISO string

-- Formatting
foreign import formatRelative :: Number -> Effect String  -- "5 min ago"
foreign import formatTime :: Number -> Effect String       -- "2:30 PM"
foreign import formatDate :: Number -> Effect String       -- "Jan 15"
foreign import formatDateTime :: Number -> Effect String   -- "Jan 15, 2:30 PM"

-- UTC Midnight calculation
foreign import getNextMidnightUTC :: Effect Number
foreign import getMsUntilMidnightUTC :: Effect Number

-- Timezone
foreign import getTimezoneOffset :: Effect Int  -- minutes
foreign import getTimezoneName :: Effect String
```

```javascript
// frontend/src/Sidepanel/FFI/DateTime.js

export function now() {
  return Date.now();
}

export function nowISO() {
  return new Date().toISOString();
}

export function formatRelative(timestamp) {
  return function() {
    const now = Date.now();
    const diff = now - timestamp;
    
    const seconds = Math.floor(diff / 1000);
    const minutes = Math.floor(seconds / 60);
    const hours = Math.floor(minutes / 60);
    const days = Math.floor(hours / 24);
    
    if (days > 0) return `${days}d ago`;
    if (hours > 0) return `${hours}h ago`;
    if (minutes > 0) return `${minutes}m ago`;
    return 'just now';
  };
}

export function formatTime(timestamp) {
  return function() {
    return new Date(timestamp).toLocaleTimeString([], { 
      hour: '2-digit', 
      minute: '2-digit' 
    });
  };
}

export function formatDate(timestamp) {
  return function() {
    return new Date(timestamp).toLocaleDateString([], { 
      month: 'short', 
      day: 'numeric' 
    });
  };
}

export function formatDateTime(timestamp) {
  return function() {
    const date = new Date(timestamp);
    return date.toLocaleDateString([], { 
      month: 'short', 
      day: 'numeric' 
    }) + ', ' + date.toLocaleTimeString([], { 
      hour: '2-digit', 
      minute: '2-digit' 
    });
  };
}

export function getNextMidnightUTC() {
  const now = new Date();
  const tomorrow = new Date(Date.UTC(
    now.getUTCFullYear(),
    now.getUTCMonth(),
    now.getUTCDate() + 1,
    0, 0, 0, 0
  ));
  return tomorrow.getTime();
}

export function getMsUntilMidnightUTC() {
  return getNextMidnightUTC()() - Date.now();
}

export function getTimezoneOffset() {
  return new Date().getTimezoneOffset();
}

export function getTimezoneName() {
  return Intl.DateTimeFormat().resolvedOptions().timeZone;
}
```

---

## Clipboard FFI

```purescript
-- frontend/src/Sidepanel/FFI/Clipboard.purs
module Sidepanel.FFI.Clipboard where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

-- Write to clipboard
foreign import writeText :: String -> Aff (Either String Unit)

-- Read from clipboard
foreign import readText :: Aff (Either String String)
```

```javascript
// frontend/src/Sidepanel/FFI/Clipboard.js

export function writeText(text) {
  return function(onError, onSuccess) {
    navigator.clipboard.writeText(text)
      .then(() => onSuccess({ tag: 'Right', value: {} }))
      .catch(e => onSuccess({ tag: 'Left', value: e.message }));
    return function(cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
}

export function readText() {
  return function(onError, onSuccess) {
    navigator.clipboard.readText()
      .then(text => onSuccess({ tag: 'Right', value: text }))
      .catch(e => onSuccess({ tag: 'Left', value: e.message }));
    return function(cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
}
```

---

## Usage Pattern

```purescript
module Example where

import Sidepanel.FFI.WebSocket as WS
import Sidepanel.FFI.Charts as Charts
import Sidepanel.FFI.Storage as Storage

-- WebSocket usage
connectAndListen :: Effect Unit
connectAndListen = do
  ws <- WS.connect "ws://localhost:3000/ws"
  
  WS.onOpen ws do
    log "Connected!"
  
  WS.onMessage ws \msg -> do
    log $ "Received: " <> msg
  
  WS.onClose ws \info -> do
    log $ "Closed: " <> show info.code

-- Chart rendering
renderUsageChart :: HTMLElement -> Array DataPoint -> Effect Unit
renderUsageChart container data_ =
  Charts.renderLineChart container
    { width: 400
    , height: 200
    , data: data_
    , xAxisKey: "timestamp"
    , lines:
        [ { dataKey: "prompt", stroke: "#8b5cf6", strokeWidth: 2, name: "Prompt", dot: false }
        , { dataKey: "completion", stroke: "#22c55e", strokeWidth: 2, name: "Completion", dot: false }
        ]
    , showGrid: true
    , showTooltip: true
    , showLegend: true
    }

-- Storage usage
savePreferences :: Preferences -> Effect Unit
savePreferences prefs = Storage.setItem "sidepanel.preferences" prefs

loadPreferences :: Effect (Maybe Preferences)
loadPreferences = Storage.getItem "sidepanel.preferences"
```

---

## Related Specifications

- `40-PURESCRIPT-ARCHITECTURE.md` - Architecture overview
- `53-TOKEN-USAGE-CHART.md` - Chart usage
- `57-TERMINAL-EMBED.md` - Terminal FFI

---

*"FFI is the bridge. Make it strong, typed, and safe."*
