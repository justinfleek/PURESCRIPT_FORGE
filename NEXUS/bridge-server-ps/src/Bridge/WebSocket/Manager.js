// WebSocket Manager FFI helpers
"use strict";

var crypto = require("crypto");

exports.generateClientId = function() {
  return function() {
    return crypto.randomBytes(8).toString("hex");
  };
};
