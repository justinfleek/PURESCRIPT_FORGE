// Node.js WebSocket Server FFI - ES Module

// Helper: Explicit default value (replaces banned || pattern)
const explicitDefault = (value, defaultValue) => {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
};

// Stub WebSocket implementation
const createWebSocketServer = (options) => {
  const connections = new Set();
  const handlers = {
    connection: []
  };
  
  return {
    on: (event, handler) => {
      if (!handlers[event]) handlers[event] = [];
      handlers[event].push(handler);
    },
    close: () => {
      connections.forEach(ws => ws.close());
      connections.clear();
    },
    _connections: connections,
    _handlers: handlers
  };
};

export const createServer = (options) => () => {
  return createWebSocketServer(options);
};

export const start = (wss) => () => {
  // Server starts automatically on creation
};

export const close = (wss) => () => {
  if (wss && wss.close) wss.close();
};

export const onConnection = (wss) => (handler) => () => {
  if (wss && wss.on) {
    wss.on("connection", (ws, req) => {
      handler(ws)(req)();
    });
  }
};

export const getRequestHeaders = (req) => () => {
  const headers = [];
  if (req && req.headers) {
    Object.keys(req.headers).forEach((key) => {
      const value = req.headers[key];
      if (value) {
        headers.push({ key: key, value: String(value) });
      }
    });
  }
  return headers;
};

export const send = (ws) => (message) => () => {
  try {
    if (ws && ws.readyState === 1) { // OPEN
      ws.send(message);
      return { tag: "Right", value: {} };
    } else {
      return { tag: "Left", value: "WebSocket not open" };
    }
  } catch (e) {
    const errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
    return { tag: "Left", value: errorMessage };
  }
};

export const closeConnection = (ws) => (code) => (reason) => () => {
  if (ws && ws.close) ws.close(code, reason);
};

export const readyState = (ws) => () => {
  return ws ? ws.readyState : 0;
};

export const onMessage = (ws) => (handler) => () => {
  if (ws && ws.on) {
    ws.on("message", (data) => {
      handler(String(data))();
    });
  }
};

export const onClose = (ws) => (handler) => () => {
  if (ws && ws.on) {
    ws.on("close", (code, reason) => {
      handler(code)(reason ? String(reason) : "")();
    });
  }
};

export const onError = (ws) => (handler) => () => {
  if (ws && ws.on) {
    ws.on("error", (error) => {
      const errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
      handler(errorMessage)();
    });
  }
};

export const ping = (ws) => (data) => () => {
  if (ws && ws.ping) ws.ping(data);
};
