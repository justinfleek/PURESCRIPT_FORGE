"use strict";

/**
 * Grep Tool FFI
 * Provides regex validation utilities
 */

// | Validate regex pattern syntax
exports.validateRegexPattern = function (pattern) {
  try {
    // Try to create a RegExp object
    new RegExp(pattern);
    return { tag: "Right", value: null };
  } catch (error) {
    return { tag: "Left", value: error.message || "Invalid regex pattern" };
  }
};
