"use strict";

/**
 * SDK Client FFI
 * Provides URI encoding utilities
 */

// | Encode URI component
exports.encodeURIComponentFFI = function (str) {
  return encodeURIComponent(str);
};
