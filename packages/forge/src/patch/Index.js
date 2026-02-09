"use strict";

/**
 * Patch Management FFI
 * Applies and reverts file patches via filesystem operations
 */

var fs = require("fs");
var path = require("path");

// | Apply patch by writing content to file
exports.applyPatchFFI = function (filePath) {
  return function (content) {
    return function (onError, onSuccess) {
      try {
        // Ensure directory exists
        var dir = path.dirname(filePath);
        if (!fs.existsSync(dir)) {
          fs.mkdirSync(dir, { recursive: true });
        }

        fs.writeFileSync(filePath, content, "utf-8");
        onSuccess({ tag: "Right", value: undefined });
      } catch (e) {
        onSuccess({ tag: "Left", value: "Failed to apply patch: " + e.message });
      }

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};
