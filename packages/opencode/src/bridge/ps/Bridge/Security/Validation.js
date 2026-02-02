// Input Validation FFI - Validation and sanitization helpers
// Production-grade input validation

// Check if string matches regex pattern
exports.matchesPattern = function(value) {
  return function(pattern) {
    try {
      const regex = new RegExp(pattern);
      return regex.test(value);
    } catch (e) {
      return false;
    }
  };
};

// Get string length
exports.length = function(value) {
  return value.length;
};

// Check if number is integer
exports.isInteger = function(value) {
  return Number.isInteger(value);
};

// Sanitize string (remove dangerous characters)
exports.sanitizeImpl = function(value) {
  // Remove null bytes, control characters, and potentially dangerous sequences
  return value
    .replace(/\0/g, '') // Remove null bytes
    .replace(/[\x00-\x1F\x7F]/g, '') // Remove control characters
    .replace(/<script/gi, '&lt;script') // Prevent script tags
    .replace(/javascript:/gi, '') // Remove javascript: protocol
    .trim();
};

// Validate JSON
exports.isValidJson = function(json) {
  try {
    JSON.parse(json);
    return true;
  } catch (e) {
    return false;
  }
};

// Validate email format
exports.isValidEmail = function(email) {
  const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
  return emailRegex.test(email);
};

// Validate URL format
exports.isValidUrl = function(url) {
  try {
    new URL(url);
    return true;
  } catch (e) {
    return false;
  }
};
