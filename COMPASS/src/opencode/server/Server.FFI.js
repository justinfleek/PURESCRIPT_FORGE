"use strict";

/**
 * Server FFI
 * Provides server utilities
 */

// | Encode value to JSON string
exports.encodeJsonToString = function (value) {
  try {
    return JSON.stringify(value);
  } catch (error) {
    return "{}";
  }
};
