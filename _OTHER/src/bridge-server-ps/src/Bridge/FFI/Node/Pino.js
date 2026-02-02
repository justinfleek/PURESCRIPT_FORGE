// Pino logger FFI
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

var pino = require("pino");

exports.create = function(options) {
  return function() {
    return pino({
      name: options.name,
      level: explicitDefault(options.level, "info"),
    });
  };
};

exports.info = function(logger) {
  return function(msg) {
    return function() {
      logger.info(msg);
    };
  };
};

exports.infoFields = function(logger) {
  return function(msg) {
    return function(fields) {
      return function() {
        logger.info(JSON.parse(fields), msg);
      };
    };
  };
};

exports.warn = function(logger) {
  return function(msg) {
    return function() {
      logger.warn(msg);
    };
  };
};

exports.warnFields = function(logger) {
  return function(msg) {
    return function(fields) {
      return function() {
        logger.warn(JSON.parse(fields), msg);
      };
    };
  };
};

exports.error = function(logger) {
  return function(msg) {
    return function() {
      logger.error(msg);
    };
  };
};

exports.errorFields = function(logger) {
  return function(msg) {
    return function(fields) {
      return function() {
        logger.error(JSON.parse(fields), msg);
      };
    };
  };
};

exports.debug = function(logger) {
  return function(msg) {
    return function() {
      logger.debug(msg);
    };
  };
};

exports.debugFields = function(logger) {
  return function(msg) {
    return function(fields) {
      return function() {
        logger.debug(JSON.parse(fields), msg);
      };
    };
  };
};
