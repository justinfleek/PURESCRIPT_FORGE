"use strict";

/**
 * FastLinter FFI
 * Provides caching and hashing utilities
 */

const crypto = require("crypto");

// | Hash content for cache key
exports.hashContent = function (content) {
  return function () {
    return crypto.createHash("sha256").update(content).digest("hex");
  };
};
