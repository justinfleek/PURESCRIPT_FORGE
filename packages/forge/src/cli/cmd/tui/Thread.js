"use strict";

/**
 * TUI Thread FFI
 * Manages the rendering thread for TUI session display
 */

// Active thread state
var activeThread = null;

// | Start TUI thread
exports.startThreadFFI = function (config) {
  return function (onError, onSuccess) {
    try {
      // Stop existing thread if any
      if (activeThread) {
        clearInterval(activeThread.timer);
      }

      activeThread = {
        sessionId: config.sessionId,
        autoScroll: config.autoScroll,
        timer: null,
      };

      // Create rendering loop
      activeThread.timer = setInterval(function () {
        // Emit render tick event
        if (typeof process !== "undefined" && process.emit) {
          process.emit("forge:tui:render", {
            sessionId: config.sessionId,
            timestamp: Date.now(),
          });
        }
      }, 100); // 10 FPS render loop

      // Don't block process exit
      if (activeThread.timer.unref) {
        activeThread.timer.unref();
      }

      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Failed to start thread: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Stop TUI thread
exports.stopThreadFFI = function (onError, onSuccess) {
  try {
    if (activeThread) {
      if (activeThread.timer) {
        clearInterval(activeThread.timer);
      }
      activeThread = null;
    }
    onSuccess({ tag: "Right", value: undefined });
  } catch (e) {
    onSuccess({ tag: "Left", value: "Failed to stop thread: " + e.message });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
