"use strict";

/**
 * Session Routes FFI
 * Provides ID generation utilities for session operations
 */

// | Generate message ID
exports.generateMessageId = function () {
  const timestamp = Date.now();
  const random = Math.floor(Math.random() * 1000000);
  return "msg_" + timestamp.toString(36) + "_" + random.toString(36);
};

// | Generate part ID
exports.generatePartId = function () {
  const timestamp = Date.now();
  const random = Math.floor(Math.random() * 1000000);
  return "part_" + timestamp.toString(36) + "_" + random.toString(36);
};

// | Get current time in milliseconds
exports.nowMillis = function () {
  return Date.now();
};
