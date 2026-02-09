// Node.js WebSocket Server FFI
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

var WebSocketServer = require("ws").WebSocketServer;

exports.createServer = function(options) {
  return function() {
    return new WebSocketServer({
      server: options.server,
      path: options.path,
    });
  };
};

exports.start = function(wss) {
  return function() {
    // Server starts automatically on creation
  };
};

exports.close = function(wss) {
  return function() {
    wss.close();
  };
};

exports.onConnection = function(wss) {
  return function(handler) {
    return function() {
      wss.on("connection", function(ws, req) {
        handler(ws)(req)();
      });
    };
  };
};

exports.getRequestHeaders = function(req) {
  return function() {
    var headers = [];
    if (req.headers) {
      Object.keys(req.headers).forEach(function(key) {
        var value = req.headers[key];
        if (value) {
          headers.push({ key: key, value: String(value) });
        }
      });
    }
    return headers;
  };
};

exports.send = function(ws) {
  return function(message) {
    return function() {
      try {
        if (ws.readyState === 1) { // OPEN
          ws.send(message);
          return { tag: "Right", value: {} };
        } else {
          return { tag: "Left", value: "WebSocket not open" };
        }
      } catch (e) {
        var errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
        return { tag: "Left", value: errorMessage };
      }
    };
  };
};

exports.closeConnection = function(ws) {
  return function(code) {
    return function(reason) {
      return function() {
        ws.close(code, reason);
      };
    };
  };
};

exports.readyState = function(ws) {
  return function() {
    return ws.readyState;
  };
};

exports.onMessage = function(ws) {
  return function(handler) {
    return function() {
      ws.on("message", function(data) {
        handler(String(data))();
      });
    };
  };
};

exports.onClose = function(ws) {
  return function(handler) {
    return function() {
      ws.on("close", function(code, reason) {
        handler(code)(reason ? String(reason) : "")();
      });
    };
  };
};

exports.onError = function(ws) {
  return function(handler) {
    return function() {
      ws.on("error", function(error) {
        var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
        handler(errorMessage)();
      });
    };
  };
};

exports.ping = function(ws) {
  return function(data) {
    return function() {
      ws.ping(data);
    };
  };
};
