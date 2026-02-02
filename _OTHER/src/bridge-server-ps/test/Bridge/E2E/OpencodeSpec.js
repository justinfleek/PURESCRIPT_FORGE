// OpenCode Integration E2E Tests FFI Implementation
"use strict";

exports.shouldContain = function(str) {
  return function(substr) {
    return str.indexOf(substr) !== -1;
  };
};

exports.shouldBeGreaterThanOrEqual = function(a) {
  return function(b) {
    return a >= b;
  };
};
