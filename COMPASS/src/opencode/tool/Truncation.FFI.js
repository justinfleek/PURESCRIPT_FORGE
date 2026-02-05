"use strict";

/**
 * Truncation Tool FFI
 * Provides file management utilities for truncation output
 */

const os = require("os");
const path = require("path");
const fs = require("fs");

// | Generate unique ID for output files
exports.generateUniqueId = function () {
  const timestamp = Date.now();
  const random = Math.floor(Math.random() * 1000000);
  return timestamp.toString(36) + "_" + random.toString(36);
};

// | Get current time in milliseconds
exports.getCurrentTime = function () {
  return Date.now();
};

// | Extract timestamp from filename (output_TIMESTAMP_random.txt)
exports.getFileTimestamp = function (filename) {
  const match = filename.match(/output_([^_]+)_/);
  if (match && match[1]) {
    const timestamp = parseInt(match[1], 36);
    return isNaN(timestamp) ? null : timestamp;
  }
  return null;
};

// | Get XDG data directory
// | Returns $XDG_DATA_HOME/opencode/tool-output or ~/.local/share/opencode/tool-output
exports.getXdgDataDir = function () {
  const xdgDataHome = process.env.XDG_DATA_HOME;
  if (xdgDataHome) {
    return path.join(xdgDataHome, "opencode", "tool-output");
  }
  
  // Fallback to ~/.local/share on Unix or AppData on Windows
  const homeDir = os.homedir();
  if (process.platform === "win32") {
    const appData = process.env.APPDATA || path.join(homeDir, "AppData", "Roaming");
    return path.join(appData, "opencode", "tool-output");
  } else {
    return path.join(homeDir, ".local", "share", "opencode", "tool-output");
  }
};

// | Ensure output directory exists
exports.ensureOutputDir = function () {
  return function () {
    return new Promise(function (resolve) {
      const dir = exports.getXdgDataDir();
      fs.mkdir(dir, { recursive: true }, function (err) {
        if (err) {
          resolve({ tag: "Left", value: err.message });
        } else {
          resolve({ tag: "Right", value: dir });
        }
      });
    });
  };
};

// | List directory contents
exports.listDirectoryFFI = function (dirPath) {
  return function () {
    return new Promise(function (resolve) {
      const fs = require("fs");
      const path = require("path");
      try {
        fs.readdir(dirPath, function (err, files) {
          if (err) {
            resolve([]); // Return empty array on error
          } else {
            // Return full paths
            const fullPaths = files.map(function (file) {
              return path.join(dirPath, file);
            });
            resolve(fullPaths);
          }
        });
      } catch (e) {
        resolve([]);
      }
    });
  };
};

// | Remove a file
exports.removeFile = function (filePath) {
  return function () {
    return new Promise(function (resolve) {
      const fs = require("fs");
      fs.unlink(filePath, function (err) {
        if (err) {
          resolve({ tag: "Left", value: err.message });
        } else {
          resolve({ tag: "Right", value: null });
        }
      });
    });
  };
};
