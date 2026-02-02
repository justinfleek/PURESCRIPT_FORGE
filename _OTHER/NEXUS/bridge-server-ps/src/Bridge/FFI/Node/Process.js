// Node.js Process FFI
"use strict";

exports.getEnv = function(key) {
  return function() {
    var value = process.env[key];
    return value === undefined ? null : value;
  };
};
