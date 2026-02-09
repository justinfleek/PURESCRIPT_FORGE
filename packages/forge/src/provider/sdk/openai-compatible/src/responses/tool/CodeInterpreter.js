"use strict";

/**
 * Code Interpreter Tool FFI
 * Executes code via language-specific interpreters
 */

var child_process = require("child_process");
var fs = require("fs");
var path = require("path");
var os = require("os");

// | Language to interpreter command mapping
var interpreters = {
  javascript: { cmd: "node", ext: ".js" },
  js: { cmd: "node", ext: ".js" },
  python: { cmd: "python3", ext: ".py" },
  py: { cmd: "python3", ext: ".py" },
  ruby: { cmd: "ruby", ext: ".rb" },
  bash: { cmd: "bash", ext: ".sh" },
  sh: { cmd: "sh", ext: ".sh" },
};

// | Execute code in specified language
exports.executeCodeFFI = function (code) {
  return function (language) {
    return function (onError, onSuccess) {
      var lang = language.toLowerCase();
      var interp = interpreters[lang];

      if (!interp) {
        onSuccess({
          tag: "Left",
          value: "Unsupported language: " + language + ". Supported: " + Object.keys(interpreters).join(", "),
        });
        return function (cancelError, onCancelerError, onCancelerSuccess) {
          onCancelerSuccess();
        };
      }

      // Write code to temp file
      var tmpDir = os.tmpdir();
      var tmpFile = path.join(tmpDir, "code-interpreter-" + Date.now() + interp.ext);

      try {
        fs.writeFileSync(tmpFile, code, "utf-8");

        var result = child_process.execSync(interp.cmd + " " + JSON.stringify(tmpFile), {
          encoding: "utf-8",
          timeout: 30000,
          maxBuffer: 10 * 1024 * 1024,
        });

        // Clean up temp file
        try { fs.unlinkSync(tmpFile); } catch (e) { /* ignore */ }

        var lines = (result || "").split("\n").filter(function (l) { return l.length > 0; });
        var lastLine = lines.length > 0 ? lines[lines.length - 1] : "";
        var logLines = lines.length > 1 ? lines.slice(0, lines.length - 1) : [];

        onSuccess({
          tag: "Right",
          value: {
            result: lastLine,
            logs: logLines,
          },
        });
      } catch (e) {
        // Clean up temp file
        try { fs.unlinkSync(tmpFile); } catch (e2) { /* ignore */ }

        if (e.status != null) {
          // Non-zero exit
          var stderr = e.stderr ? e.stderr.toString() : "";
          var stdout = e.stdout ? e.stdout.toString() : "";
          onSuccess({
            tag: "Right",
            value: {
              result: stderr || "Exit code: " + e.status,
              logs: stdout.split("\n").filter(function (l) { return l.length > 0; }),
            },
          });
        } else {
          onSuccess({
            tag: "Left",
            value: "Code execution failed: " + e.message,
          });
        }
      }

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};
