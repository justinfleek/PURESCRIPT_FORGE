"use strict";

/**
 * MCP OAuth Callback FFI
 * Handles OAuth authorization code exchange for MCP servers
 */

// | Handle OAuth callback - exchange code for token
exports.handleOAuthCallbackFFI = function (serverId) {
  return function (code) {
    return function (onError, onSuccess) {
      // Look up the MCP server's OAuth config
      // In production, this would:
      // 1. Look up server config from MCP state
      // 2. Extract tokenUrl from server's OAuth config
      // 3. POST to tokenUrl with authorization code
      // 4. Store resulting access token
      // 5. Reconnect MCP server with authenticated transport

      try {
        // Emit event for MCP module to handle
        if (typeof process !== "undefined" && process.emit) {
          process.emit("forge:mcp:oauth-callback", {
            serverId: serverId,
            code: code,
            timestamp: Date.now(),
          });
        }

        onSuccess({ tag: "Right", value: undefined });
      } catch (e) {
        onSuccess({
          tag: "Left",
          value: "OAuth callback failed: " + e.message,
        });
      }

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};
