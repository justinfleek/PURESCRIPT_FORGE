// Security Headers FFI - HTTP security headers middleware
// Production-grade security headers

// Add all security headers
export const addSecurityHeadersImpl = function(response) {
  return function(config) {
    return function() {
      // Set all security headers
      response.setHeader('Content-Security-Policy', config.contentSecurityPolicy);
      response.setHeader('X-Frame-Options', config.frameOptions);
      response.setHeader('X-Content-Type-Options', config.contentTypeOptions);
      response.setHeader('Strict-Transport-Security', config.strictTransportSecurity);
      response.setHeader('X-XSS-Protection', config.xssProtection);
    };
  };
};

// Set header helper
export const setHeader = function(response) {
  return function(name) {
    return function(value) {
      return function() {
        response.setHeader(name, value);
      };
    };
  };
};
