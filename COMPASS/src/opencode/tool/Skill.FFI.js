"use strict";

/**
 * Skill FFI
 * Reuses directory listing from Ls tool
 */

const fs = require("fs");
const path = require("path");
const { promisify } = require("util");

const readdirAsync = promisify(fs.readdir);
const statAsync = promisify(fs.stat);

/**
 * List directory contents (reused from Ls.FFI)
 */
exports.listDirectory = function (dirPath) {
  return async function () {
    try {
      const entries = await readdirAsync(dirPath);
      const results = await Promise.all(
        entries.map(async (name) => {
          const fullPath = path.join(dirPath, name);
          try {
            const stat = await statAsync(fullPath);
            return {
              name: name,
              isDirectory: stat.isDirectory(),
            };
          } catch (err) {
            // Skip entries we can't stat
            return null;
          }
        })
      );
      
      // Filter out null entries
      const validResults = results.filter((r) => r !== null);
      
      return {
        tag: "Right",
        value: validResults,
      };
    } catch (error) {
      return {
        tag: "Left",
        value: error.message || "Failed to list directory",
      };
    }
  };
};
