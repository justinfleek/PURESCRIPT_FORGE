"use strict";

/**
 * TUI Worker FFI
 * Manages background worker for TUI processing
 */

var workerActive = false;

// | Start worker
exports.startWorkerFFI = function (onError, onSuccess) {
  try {
    workerActive = true;

    // Emit worker started event
    if (typeof process !== "undefined" && process.emit) {
      process.emit("forge:tui:worker-started", { timestamp: Date.now() });
    }

    onSuccess({ tag: "Right", value: undefined });
  } catch (e) {
    onSuccess({ tag: "Left", value: "Failed to start worker: " + e.message });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};

// | Send message to worker
exports.sendWorkerMessageFFI = function (message) {
  return function (onError, onSuccess) {
    try {
      if (!workerActive) {
        onSuccess({ tag: "Left", value: "Worker not running" });
        return function (c, ce, cs) { cs(); };
      }

      // Parse and dispatch message
      if (message === "shutdown") {
        workerActive = false;
        if (typeof process !== "undefined" && process.emit) {
          process.emit("forge:tui:worker-stopped", { timestamp: Date.now() });
        }
      } else if (message === "init") {
        // Re-initialize worker state
      } else if (message.startsWith("process:")) {
        var payload = message.slice(8);
        // Emit processing event
        if (typeof process !== "undefined" && process.emit) {
          process.emit("forge:tui:worker-process", {
            payload: payload,
            timestamp: Date.now(),
          });
        }
      }

      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Worker message failed: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};
