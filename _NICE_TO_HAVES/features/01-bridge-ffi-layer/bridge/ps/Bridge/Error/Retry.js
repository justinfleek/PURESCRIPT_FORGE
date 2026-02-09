// Retry Logic FFI - Exponential backoff helpers
// Production-grade retry mechanism

// Generate random integer in range [min, max)
exports.randomRange = function(min) {
  return function(max) {
    return function() {
      return Math.floor(Math.random() * (max - min)) + min;
    };
  };
};
