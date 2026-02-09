"use strict";

/**
 * Transcript FFI
 * Exports transcript content to files
 */

var fs = require("fs");
var path = require("path");

// | Write transcript to file
exports.writeTranscriptFFI = function (filePath) {
  return function (content) {
    return function (onError, onSuccess) {
      try {
        var dir = path.dirname(filePath);
        if (!fs.existsSync(dir)) {
          fs.mkdirSync(dir, { recursive: true });
        }

        fs.writeFileSync(filePath, content, "utf-8");
        onSuccess({ tag: "Right", value: undefined });
      } catch (e) {
        onSuccess({ tag: "Left", value: "Failed to export transcript: " + e.message });
      }

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};
