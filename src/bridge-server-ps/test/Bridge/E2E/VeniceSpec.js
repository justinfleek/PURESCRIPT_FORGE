// Venice API E2E Tests FFI Implementation
"use strict";

exports.shouldBeGreaterThanOrEqual = function(a) {
  return function(b) {
    return a >= b;
  };
};
