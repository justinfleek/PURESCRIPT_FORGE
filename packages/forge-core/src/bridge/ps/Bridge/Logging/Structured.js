// Structured Logging FFI - Correlation IDs and structured logging
// Production-grade logging with correlation IDs

const crypto = require('crypto');

// Generate UUID v4
exports.generateUUID = function() {
  return crypto.randomUUID();
};

// Log with level and correlation ID
exports.logWithLevel = function(logger) {
  return function(level) {
    return function(message) {
      return function(data) {
        return function() {
          const logData = {
            correlationId: logger.correlationId,
            message: message,
            ...(data ? JSON.parse(data) : {})
          };
          
          switch (level) {
            case 'info':
              logger.baseLogger.info(logData);
              break;
            case 'error':
              logger.baseLogger.error(logData);
              break;
            case 'warn':
              logger.baseLogger.warn(logData);
              break;
            case 'debug':
              logger.baseLogger.debug(logData);
              break;
            default:
              logger.baseLogger.info(logData);
          }
        };
      };
    };
  };
};

// Create child logger with context
exports.createChildLogger = function(baseLogger) {
  return function(context) {
    return function() {
      const contextData = JSON.parse(context);
      return baseLogger.child(contextData);
    };
  };
};
