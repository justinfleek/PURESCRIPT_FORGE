// Database Sync FFI Implementation
"use strict";

exports.getCurrentTimeMillis = function() {
  return function() {
    return Date.now();
  };
};

exports.trySync = function(aff) {
  return function() {
    return aff().catch(function(err) {
      var errorMessage = err.message !== undefined && err.message !== null ? err.message : String(err);
      return { tag: "Left", value: errorMessage };
    }).then(function(result) {
      if (result && result.tag === "Left") {
        return result;
      }
      return { tag: "Right", value: result };
    });
  };
};
