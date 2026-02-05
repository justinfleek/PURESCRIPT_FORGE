"use strict";

/**
 * Code Smell Detector FFI utilities
 */

/**
 * Parse number from string
 */
exports.parseNumberFFI = function (str) {
  const parsed = parseFloat(str);
  return isNaN(parsed) ? 0.0 : parsed;
};
