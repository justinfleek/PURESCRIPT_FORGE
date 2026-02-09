// WebSocket E2E Tests FFI Implementation
"use strict";

exports.shouldContain = function(str) {
  return function(substr) {
    return str.indexOf(substr) !== -1;
  };
};

exports.shouldNotContain = function(str) {
  return function(substr) {
    return str.indexOf(substr) === -1;
  };
};
