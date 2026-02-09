"use strict";

/**
 * TUI Attach FFI
 * Connects to a running forge server via WebSocket
 */

var activeConnection = null;

// | Attach to server
exports.attachToServerFFI = function (config) {
  return function (onError, onSuccess) {
    try {
      // Dynamic import for WebSocket (Node.js)
      var WebSocket;
      try {
        WebSocket = require("ws");
      } catch (e) {
        // Fallback to globalThis.WebSocket (browser/Deno)
        WebSocket = globalThis.WebSocket;
      }

      if (!WebSocket) {
        onSuccess({ tag: "Left", value: "WebSocket not available" });
        return function (c, ce, cs) { cs(); };
      }

      var url = config.serverUrl.replace(/^http/, "ws") + "/ws?session=" + config.sessionId;
      var ws = new WebSocket(url);

      ws.onopen = function () {
        activeConnection = ws;

        // Send attach message
        ws.send(JSON.stringify({
          type: "attach",
          sessionId: config.sessionId,
        }));

        onSuccess({ tag: "Right", value: undefined });
      };

      ws.onerror = function (err) {
        onSuccess({
          tag: "Left",
          value: "WebSocket connection failed: " + (err.message || "unknown error"),
        });
      };

      ws.onclose = function () {
        activeConnection = null;
      };
    } catch (e) {
      onSuccess({ tag: "Left", value: "Attach failed: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Detach from server
exports.detachFFI = function (onError, onSuccess) {
  try {
    if (activeConnection) {
      activeConnection.close();
      activeConnection = null;
    }
    onSuccess({ tag: "Right", value: undefined });
  } catch (e) {
    onSuccess({ tag: "Left", value: "Detach failed: " + e.message });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
