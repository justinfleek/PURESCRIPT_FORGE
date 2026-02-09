"use strict";

/**
 * Local Shell Tool FFI
 * Executes shell commands via child_process.execSync
 */

var child_process = require("child_process");

// | Execute shell command and return stdout/stderr/exitCode
exports.executeShellFFI = function (command) {
  return function (cwd) {
    return function (timeout) {
      return function (onError, onSuccess) {
        try {
          var options = {
            encoding: "utf-8",
            maxBuffer: 10 * 1024 * 1024,
            shell: true,
          };

          if (cwd != null) {
            options.cwd = cwd;
          }

          if (timeout != null) {
            options.timeout = timeout;
          }

          var stdout = child_process.execSync(command, options);

          onSuccess({
            tag: "Right",
            value: {
              stdout: stdout || "",
              stderr: "",
              exitCode: 0,
            },
          });
        } catch (e) {
          // execSync throws on non-zero exit
          if (e.status != null) {
            onSuccess({
              tag: "Right",
              value: {
                stdout: e.stdout ? e.stdout.toString() : "",
                stderr: e.stderr ? e.stderr.toString() : "",
                exitCode: e.status,
              },
            });
          } else {
            onSuccess({
              tag: "Left",
              value: "Shell execution failed: " + e.message,
            });
          }
        }

        return function (cancelError, onCancelerError, onCancelerSuccess) {
          onCancelerSuccess();
        };
      };
    };
  };
};
