// Database Sync FFI Implementation


export const getCurrentTimeMillis = function() {
  return function() {
    return Date.now();
  };
};

export const trySync = function(aff) {
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
