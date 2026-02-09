"use strict";

/**
 * Clipboard FFI
 * Uses platform-specific clipboard commands
 */

var child_process = require("child_process");

// | Copy text to system clipboard
exports.copyToClipboardFFI = function (text) {
  return function (onError, onSuccess) {
    try {
      var platform = process.platform;
      var cmd;

      if (platform === "darwin") {
        cmd = "pbcopy";
      } else if (platform === "win32") {
        cmd = "clip";
      } else {
        // Linux: try xclip, then xsel, then wl-copy
        cmd = "xclip -selection clipboard";
      }

      var proc = child_process.spawn(cmd.split(" ")[0], cmd.split(" ").slice(1), {
        stdio: ["pipe", "ignore", "ignore"],
        shell: platform === "win32",
      });

      proc.stdin.write(text);
      proc.stdin.end();

      proc.on("close", function (code) {
        if (code === 0) {
          onSuccess({ tag: "Right", value: undefined });
        } else {
          onSuccess({ tag: "Left", value: "Clipboard command exited with code " + code });
        }
      });

      proc.on("error", function (err) {
        onSuccess({ tag: "Left", value: "Clipboard not available: " + err.message });
      });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Clipboard copy failed: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Read text from system clipboard
exports.pasteFromClipboardFFI = function (onError, onSuccess) {
  try {
    var platform = process.platform;
    var cmd;

    if (platform === "darwin") {
      cmd = "pbpaste";
    } else if (platform === "win32") {
      cmd = "powershell.exe -command Get-Clipboard";
    } else {
      cmd = "xclip -selection clipboard -o";
    }

    var result = child_process.execSync(cmd, {
      encoding: "utf-8",
      timeout: 5000,
      shell: true,
    });

    onSuccess({ tag: "Right", value: result || "" });
  } catch (e) {
    onSuccess({ tag: "Left", value: "Clipboard paste failed: " + e.message });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
