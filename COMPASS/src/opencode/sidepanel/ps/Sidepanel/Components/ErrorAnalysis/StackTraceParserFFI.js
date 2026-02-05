"use strict";

/**
 * Stack trace parser FFI utilities
 */

/**
 * Parse integer from string
 */
exports.parseIntFFI = function (str) {
  const parsed = parseInt(str, 10);
  return isNaN(parsed) ? 0 : parsed;
};
