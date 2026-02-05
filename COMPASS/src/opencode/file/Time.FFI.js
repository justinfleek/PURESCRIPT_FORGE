"use strict";

/**
 * File Time FFI
 * Provides file time utilities
 */

const fs = require("fs").promises;

// | Get file statistics (times)
exports.getFileStats = function (filePath) {
  return function () {
    return fs.stat(filePath)
      .then(function (stats) {
        return {
          tag: "Right",
          value: {
            created: stats.birthtimeMs || stats.ctimeMs,
            modified: stats.mtimeMs,
            accessed: stats.atimeMs
          }
        };
      })
      .catch(function (error) {
        return {
          tag: "Left",
          value: error.message || "Failed to get file stats"
        };
      });
  };
};

// | Touch a file (update modified time)
exports.touchFile = function (filePath) {
  return function () {
    const now = Date.now();
    return fs.utimes(filePath, now / 1000, now / 1000)
      .then(function () {
        return {
          tag: "Right",
          value: null
        };
      })
      .catch(function (error) {
        return {
          tag: "Left",
          value: error.message || "Failed to touch file"
        };
      });
  };
};
