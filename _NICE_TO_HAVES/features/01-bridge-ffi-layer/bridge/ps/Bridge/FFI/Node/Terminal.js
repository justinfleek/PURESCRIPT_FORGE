// Terminal Execution FFI Implementation
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

const { spawn } = require("child_process");
const path = require("path");

// | Execute terminal command
exports.executeCommand = function(command) {
  return function(cwd) {
    return function(sessionId) {
      return function(onError, onSuccess) {
        return function() {
          const cwdPath = explicitDefault(cwd, process.cwd());
          
          // Parse command properly (handles quoted strings, escaped characters)
          function parseCommand(cmdStr) {
            const parts = [];
            let current = '';
            let inQuotes = false;
            let quoteChar = null;
            let escapeNext = false;
            
            for (let i = 0; i < cmdStr.length; i++) {
              const char = cmdStr[i];
              
              if (escapeNext) {
                current += char;
                escapeNext = false;
                continue;
              }
              
              if (char === '\\') {
                escapeNext = true;
                continue;
              }
              
              if ((char === '"' || char === "'") && !inQuotes) {
                inQuotes = true;
                quoteChar = char;
                continue;
              }
              
              if (char === quoteChar && inQuotes) {
                inQuotes = false;
                quoteChar = null;
                continue;
              }
              
              if (char === ' ' && !inQuotes) {
                if (current.length > 0) {
                  parts.push(current);
                  current = '';
                }
                continue;
              }
              
              current += char;
            }
            
            if (current.length > 0) {
              parts.push(current);
            }
            
            return parts;
          }
          
          const parts = parseCommand(command.trim());
          const cmd = parts[0];
          const args = parts.slice(1);
          
          const proc = spawn(cmd, args, {
            cwd: cwdPath,
            shell: true,
            stdio: ["pipe", "pipe", "pipe"]
          });
          
          let stdout = "";
          let stderr = "";
          
          proc.stdout.on("data", function(data) {
            stdout += data.toString();
          });
          
          proc.stderr.on("data", function(data) {
            stderr += data.toString();
          });
          
          proc.on("close", function(code) {
            if (code === 0) {
              onSuccess({
                success: true,
                output: explicitDefault(stdout, null),
                exitCode: code
              })();
            } else {
              onError("Command failed with exit code " + code + ": " + stderr)();
            }
          });
          
          proc.on("error", function(err) {
            onError("Failed to execute command: " + err.message)();
          });
          
          return function(cancelError, cancelerError, cancelerSuccess) {
            proc.kill();
            cancelerSuccess()();
          };
        };
      };
    };
  };
};
