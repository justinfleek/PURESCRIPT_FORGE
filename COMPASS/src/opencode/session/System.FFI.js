"use strict";

/**
 * Session System FFI
 * Provides environment information for system messages
 */

const os = require("os");
const process = require("process");

// | Get platform name
exports.getPlatform = function () {
  return process.platform;
};

// | Get current date as string
exports.getCurrentDate = function () {
  return new Date().toDateString();
};

// | Get current working directory
exports.getCurrentWorkingDirectory = function () {
  return process.cwd();
};
