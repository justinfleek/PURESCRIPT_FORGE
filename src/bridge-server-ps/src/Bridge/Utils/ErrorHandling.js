// Error Handling Utilities FFI Implementation


export const message = function(err) {
  return err.message !== undefined && err.message !== null ? err.message : String(err);
};

export const delayImpl = function(ms) {
  return function() {
    return new Promise(function(resolve) {
      setTimeout(resolve, ms);
    });
  };
};
