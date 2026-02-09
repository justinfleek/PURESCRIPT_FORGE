"use strict";

/**
 * Editor FFI
 * Opens files in the user's preferred editor
 */

var child_process = require("child_process");

// | Detect editor from environment
function detectEditor() {
  // Check environment variables in priority order
  var envVars = ["VISUAL", "EDITOR"];
  for (var i = 0; i < envVars.length; i++) {
    var editor = process.env[envVars[i]];
    if (editor) return editor;
  }

  // Check for common editors
  var editors = ["code", "vim", "nvim", "nano", "emacs", "vi"];
  for (var j = 0; j < editors.length; j++) {
    try {
      child_process.execSync("which " + editors[j], {
        stdio: "ignore",
        timeout: 3000,
      });
      return editors[j];
    } catch (e) {
      // Not found, continue
    }
  }

  return null;
}

// | Open file in editor
exports.openInEditorFFI = function (filePath) {
  return function (onError, onSuccess) {
    try {
      var editor = detectEditor();
      if (!editor) {
        onSuccess({ tag: "Left", value: "No editor found. Set EDITOR or VISUAL environment variable." });
        return function (c, ce, cs) { cs(); };
      }

      // Some editors support line number arguments
      var proc = child_process.spawn(editor, [filePath], {
        stdio: "inherit",
        detached: false,
      });

      proc.on("close", function (code) {
        if (code === 0) {
          onSuccess({ tag: "Right", value: undefined });
        } else {
          onSuccess({ tag: "Left", value: "Editor exited with code " + code });
        }
      });

      proc.on("error", function (err) {
        onSuccess({ tag: "Left", value: "Failed to open editor: " + err.message });
      });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Failed to open editor: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Open file at specific line
exports.openInEditorAtLineFFI = function (filePath) {
  return function (line) {
    return function (onError, onSuccess) {
      try {
        var editor = detectEditor();
        if (!editor) {
          onSuccess({ tag: "Left", value: "No editor found. Set EDITOR or VISUAL environment variable." });
          return function (c, ce, cs) { cs(); };
        }

        var args;
        // Handle editor-specific line number arguments
        if (editor.includes("code")) {
          args = ["--goto", filePath + ":" + line];
        } else if (editor.includes("vim") || editor.includes("nvim") || editor.includes("vi")) {
          args = ["+" + line, filePath];
        } else if (editor.includes("emacs")) {
          args = ["+" + line, filePath];
        } else if (editor.includes("nano")) {
          args = ["+" + line, filePath];
        } else {
          args = [filePath];
        }

        var proc = child_process.spawn(editor, args, {
          stdio: "inherit",
          detached: false,
        });

        proc.on("close", function (code) {
          if (code === 0) {
            onSuccess({ tag: "Right", value: undefined });
          } else {
            onSuccess({ tag: "Left", value: "Editor exited with code " + code });
          }
        });

        proc.on("error", function (err) {
          onSuccess({ tag: "Left", value: "Failed to open editor: " + err.message });
        });
      } catch (e) {
        onSuccess({ tag: "Left", value: "Failed to open editor: " + e.message });
      }

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};

// | Get editor command
exports.getEditorCommandFFI = function (onError, onSuccess) {
  var editor = detectEditor();
  if (editor) {
    onSuccess(editor);  // Just String (Maybe is handled PS-side)
  } else {
    onSuccess(null);
  }
  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
