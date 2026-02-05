"use strict";

/**
 * Task Tool FFI
 * Provides session ID generation and timestamp utilities
 */

// | Generate a unique session ID
exports.generateSessionId = function () {
  const timestamp = Date.now();
  const random = Math.floor(Math.random() * 10000);
  return "task_" + timestamp + "_" + random;
};

// | Get current timestamp in milliseconds
exports.nowMillis = function () {
  return Date.now();
};
