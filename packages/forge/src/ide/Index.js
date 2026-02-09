"use strict";

/**
 * IDE detection FFI
 * Detects IDE from environment variables and running processes
 */

var child_process = require("child_process");

// | Detect IDE from environment
exports.detectIDEFFI = function (onError, onSuccess) {
  try {
    // Check VS Code / Cursor specific env vars
    if (process.env.TERM_PROGRAM === "vscode") {
      // Check if it's Cursor (fork of VS Code)
      if (process.env.CURSOR_CHANNEL || (process.env.TERM_PROGRAM_VERSION || "").includes("cursor")) {
        onSuccess({ value0: "cursor" }); // Just Cursor
      } else {
        onSuccess({ value0: "vscode" }); // Just VSCode
      }
      return function (c, ce, cs) { cs(); };
    }

    // Check JetBrains terminal
    if (process.env.TERMINAL_EMULATOR === "JetBrains-JediTerm" || process.env.JETBRAINS_IDE) {
      onSuccess({ value0: "jetbrains" });
      return function (c, ce, cs) { cs(); };
    }

    // Check Vim/Neovim
    if (process.env.VIM || process.env.NVIM || process.env.NVIM_LISTEN_ADDRESS) {
      onSuccess({ value0: "vim" });
      return function (c, ce, cs) { cs(); };
    }

    // Check Emacs
    if (process.env.INSIDE_EMACS || process.env.EMACS) {
      onSuccess({ value0: "emacs" });
      return function (c, ce, cs) { cs(); };
    }

    // No IDE detected
    onSuccess(null); // Nothing
  } catch (e) {
    onSuccess(null);
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};

// | Open file in IDE
exports.openFileInIDEFFI = function (filePath) {
  return function (line) {
    return function (onError, onSuccess) {
      try {
        var cmd;
        var args;

        // Try VS Code / Cursor first (most common)
        if (process.env.TERM_PROGRAM === "vscode") {
          cmd = process.env.CURSOR_CHANNEL ? "cursor" : "code";
          args = line != null ? ["--goto", filePath + ":" + line] : [filePath];
        } else if (process.env.TERMINAL_EMULATOR === "JetBrains-JediTerm") {
          // JetBrains uses its own remote dev protocol
          cmd = "idea";
          args = line != null ? ["--line", String(line), filePath] : [filePath];
        } else {
          // Fallback to VS Code if installed
          cmd = "code";
          args = line != null ? ["--goto", filePath + ":" + line] : [filePath];
        }

        var proc = child_process.spawn(cmd, args, {
          stdio: "ignore",
          detached: true,
        });

        proc.unref();

        proc.on("error", function (err) {
          onSuccess({ tag: "Left", value: "Failed to open in IDE: " + err.message });
        });

        // Give it a moment to start
        setTimeout(function () {
          onSuccess({ tag: "Right", value: undefined });
        }, 200);
      } catch (e) {
        onSuccess({ tag: "Left", value: "Failed to open in IDE: " + e.message });
      }

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};
