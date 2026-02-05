"use strict";

/**
 * Filesystem FFI
 * Provides filesystem utilities
 */

const fs = require("fs").promises;
const path = require("path");

// | Stat a path
exports.statPath = function (filePath) {
  return function () {
    return fs.stat(filePath)
      .then(function (stats) {
        return {
          tag: "Right",
          value: {
            isDirectory: stats.isDirectory(),
            size: stats.size
          }
        };
      })
      .catch(function (error) {
        return {
          tag: "Left",
          value: error.message || "Failed to stat path"
        };
      });
  };
};

// | Read directory
exports.readDirectory = function (dirPath) {
  return function () {
    return fs.readdir(dirPath)
      .then(function (files) {
        return {
          tag: "Right",
          value: files
        };
      })
      .catch(function (error) {
        return {
          tag: "Left",
          value: error.message || "Failed to read directory"
        };
      });
  };
};

// | Create directory recursively
exports.makeDirectoryRecursive = function (dirPath) {
  return function () {
    return fs.mkdir(dirPath, { recursive: true })
      .then(function () {
        return {
          tag: "Right",
          value: null
        };
      })
      .catch(function (error) {
        return {
          tag: "Left",
          value: error.message || "Failed to create directory"
        };
      });
  };
};
