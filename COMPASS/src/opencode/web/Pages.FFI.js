"use strict";

/**
 * Web Pages FFI
 * Provides Astro content collection access
 */

// Note: This would integrate with Astro's getCollection API
// For now, this is a placeholder that would need Astro runtime integration
exports.getDocsCollection = function () {
  return function () {
    return Promise.resolve([]);
  };
};
