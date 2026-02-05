"use strict";

/**
 * Wildcard FFI
 * Provides wildcard pattern matching utilities
 */

// | Match a string against a wildcard pattern
exports.matchWildcard = function (pattern) {
  return function (str) {
    // Convert wildcard pattern to regex
    const regexPattern = pattern
      .replace(/[.+^${}()|[\]\\]/g, "\\$&") // Escape special regex chars
      .replace(/\*/g, ".*")                  // * matches any sequence
      .replace(/\?/g, ".");                  // ? matches single char
    
    const regex = new RegExp("^" + regexPattern + "$");
    return regex.test(str);
  };
};

// | Convert wildcard pattern to regex string
exports.convertWildcardToRegex = function (pattern) {
  return pattern
    .replace(/[.+^${}()|[\]\\]/g, "\\$&") // Escape special regex chars
    .replace(/\*/g, ".*")                  // * matches any sequence
    .replace(/\?/g, ".");                  // ? matches single char
};
