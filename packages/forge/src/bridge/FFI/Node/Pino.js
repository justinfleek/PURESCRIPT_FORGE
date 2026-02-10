// Pino Logger FFI - Forward Declaration
// Full implementation in bridge/ batch (Batch 7)
"use strict";

exports.info = function(logger) {
  return function(message) {
    return function() {
      if (logger && typeof logger.info === 'function') {
        logger.info(message);
      } else {
        console.log('[INFO]', message);
      }
    };
  };
};

exports.error = function(logger) {
  return function(message) {
    return function() {
      if (logger && typeof logger.error === 'function') {
        logger.error(message);
      } else {
        console.error('[ERROR]', message);
      }
    };
  };
};

exports.warn = function(logger) {
  return function(message) {
    return function() {
      if (logger && typeof logger.warn === 'function') {
        logger.warn(message);
      } else {
        console.warn('[WARN]', message);
      }
    };
  };
};

exports.debug = function(logger) {
  return function(message) {
    return function() {
      if (logger && typeof logger.debug === 'function') {
        logger.debug(message);
      } else {
        console.debug('[DEBUG]', message);
      }
    };
  };
};
