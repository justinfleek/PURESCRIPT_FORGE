"use strict";

/**
 * ID Generation FFI
 * Provides unique ID generation utilities
 */

const crypto = require("crypto");

// | Generate UUID v4
exports.generateUUID = function () {
  return crypto.randomUUID();
};

// | Generate short ID (base62, 8 characters)
exports.generateShortId = function () {
  const chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
  let result = "";
  const randomBytes = crypto.randomBytes(8);
  for (let i = 0; i < 8; i++) {
    result += chars[randomBytes[i] % chars.length];
  }
  return result;
};
