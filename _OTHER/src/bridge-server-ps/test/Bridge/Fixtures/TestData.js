// Test Data FFI Implementation
"use strict";

exports.getCurrentDateTime = function() {
  return function() {
    return new Date().toISOString();
  };
};
