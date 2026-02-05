"use strict";

const fs = require("fs");
const { promisify } = require("util");

const readFileAsync = promisify(fs.readFile);
const writeFileAsync = promisify(fs.writeFile);
const unlinkAsync = promisify(fs.unlink);

/**
 * Read file content
 */
exports.readFile = function (filePath) {
  return async function () {
    try {
      const content = await readFileAsync(filePath, "utf8");
      return { tag: "Right", value: content };
    } catch (error) {
      return { tag: "Left", value: error.message || "Failed to read file" };
    }
  };
};

/**
 * Write file content
 */
exports.writeFile = function (filePath) {
  return function (content) {
    return async function () {
      try {
        await writeFileAsync(filePath, content, "utf8");
        return { tag: "Right", value: undefined };
      } catch (error) {
        return { tag: "Left", value: error.message || "Failed to write file" };
      }
    };
  };
};

/**
 * Delete a file
 */
exports.deleteFile = function (filePath) {
  return async function () {
    try {
      await unlinkAsync(filePath);
      return { tag: "Right", value: undefined };
    } catch (error) {
      return { tag: "Left", value: error.message || "Failed to delete file" };
    }
  };
};
