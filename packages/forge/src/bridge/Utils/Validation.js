// Validation Utilities FFI Implementation
"use strict";

exports.length = function(s) {
  return s.length;
};

exports.contains = function(substr) {
  return function(str) {
    return str.indexOf(substr) !== -1;
  };
};
