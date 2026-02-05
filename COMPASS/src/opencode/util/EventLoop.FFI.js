"use strict";

/**
 * Event Loop FFI
 * Provides event loop utilities
 */

const process = require("process");

// | Schedule on next tick
exports.processNextTick = function (action) {
  return function () {
    process.nextTick(function () {
      action();
    });
  };
};

// | Schedule with setImmediate
exports.scheduleImmediate = function (action) {
  return function () {
    setImmediate(function () {
      action();
    });
  };
};

// | Keep event loop alive
exports.keepAliveLoop = function () {
  // Create a ref that keeps the event loop alive
  const ref = setInterval(function () {}, 10000);
  // Note: In production, would need proper cleanup mechanism
  return ref;
};
