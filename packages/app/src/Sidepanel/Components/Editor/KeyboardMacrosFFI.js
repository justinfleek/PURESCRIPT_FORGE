"use strict";

/**
 * Keyboard Macros FFI utilities
 */

/**
 * Parse integer from string
 */
exports.parseIntFFI = function (str) {
  var parsed = parseInt(str, 10);
  if (isNaN(parsed)) {
    return 0;
  }
  return parsed;
};
