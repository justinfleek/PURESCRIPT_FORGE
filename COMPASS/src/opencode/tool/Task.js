// Task Tool FFI
"use strict";

const crypto = require("crypto");

// | Generate session ID
exports.generateSessionId = function() {
  return "task_" + crypto.randomUUID().replace(/-/g, "").slice(0, 16);
};
