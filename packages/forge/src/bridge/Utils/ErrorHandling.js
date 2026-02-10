// Error Handling Utilities FFI Implementation
"use strict";

exports.message = function(err) {
  return err.message !== undefined && err.message !== null ? err.message : String(err);
};

exports.delayImpl = function(ms) {
  return function() {
    return new Promise(function(resolve) {
      setTimeout(resolve, ms);
    });
  };
};
