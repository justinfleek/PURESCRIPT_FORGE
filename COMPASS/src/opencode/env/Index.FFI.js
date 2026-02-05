"use strict";

/**
 * Environment FFI
 * Provides environment variable utilities
 */

// | Set an environment variable
exports.setEnv = function (key) {
  return function (value) {
    return function () {
      process.env[key] = value;
    };
  };
};
