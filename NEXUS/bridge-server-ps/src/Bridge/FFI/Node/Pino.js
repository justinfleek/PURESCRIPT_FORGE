// Pino logger FFI
"use strict";

var pino = require("pino");

exports.create = function(options) {
  return function() {
    return pino({
      name: options.name,
      level: options.level || "info",
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

exports.error = function(logger) {
  return function(msg) {
    return function() {
      logger.error(msg);
    };
  };
};
