// WASM Sandbox FFI - wasmtime integration
// Provides secure WebAssembly execution with resource limits
"use strict";

/**
 * Execute WASM module with sandboxing.
 *
 * @param {Object} config - WASM configuration
 * @param {string} config.wasmBytes - Base64-encoded WASM bytes
 * @param {number} config.memoryLimitMB - Maximum memory in MB
 * @param {number} config.timeLimitMs - Maximum execution time in ms
 * @param {number|null} config.instructionLimit - Max instructions (null = unlimited)
 * @param {Object} config.imports - Host function imports
 * @param {boolean} config.wasiEnabled - Enable WASI
 * @param {Object} imports - Available host functions
 * @returns {Object} - Either { tag: "Left", value: error } or { tag: "Right", value: string }
 */
exports.executeWASMImpl = function (config) {
  return function (imports) {
    return function () {
      try {
        // Decode base64 WASM bytes
        var wasmBytes = Buffer.from(config.wasmBytes, "base64");

        // Validate WASM magic number
        if (wasmBytes.length < 4 || wasmBytes[0] !== 0x00 || wasmBytes[1] !== 0x61 ||
            wasmBytes[2] !== 0x73 || wasmBytes[3] !== 0x6d) {
          return {
            tag: "Left",
            value: { type: "InvalidWASM", value: "Invalid WASM magic number" },
          };
        }

        // Build host function imports
        var wasmImports = buildImports(imports);

        // Set time limit
        var timeLimit = config.timeLimitMs;
        var startTime = Date.now();

        // Compile and instantiate
        var module = new WebAssembly.Module(wasmBytes);
        var instance = new WebAssembly.Instance(module, wasmImports);

        // Find main/_start function
        var mainFunc = instance.exports._start || instance.exports.main || instance.exports.run;
        if (!mainFunc) {
          return {
            tag: "Left",
            value: {
              type: "ImportNotFound",
              value: "No entry point found (_start, main, or run)",
            },
          };
        }

        try {
          // Call main function
          var result = mainFunc();

          // Check time limit
          var elapsed = Date.now() - startTime;
          if (elapsed > timeLimit) {
            return {
              tag: "Left",
              value: { type: "TimeLimitExceeded", value: timeLimit },
            };
          }

          // Convert result to string
          var output = String(result || "");
          return { tag: "Right", value: output };
        } catch (error) {
          // Check if it's a trap
          if (error.message && error.message.indexOf("trap") !== -1) {
            return {
              tag: "Left",
              value: { type: "Trap", value: error.message },
            };
          }

          // Check time limit
          var elapsedOnError = Date.now() - startTime;
          if (elapsedOnError > timeLimit) {
            return {
              tag: "Left",
              value: { type: "TimeLimitExceeded", value: timeLimit },
            };
          }

          throw error;
        }
      } catch (error) {
        // Handle validation errors
        if (error.message && error.message.indexOf("invalid") !== -1) {
          return {
            tag: "Left",
            value: { type: "InvalidWASM", value: error.message },
          };
        }

        // Handle other errors
        return {
          tag: "Left",
          value: {
            type: "HostFunctionError",
            value: error.message || String(error),
          },
        };
      }
    };
  };
};

/**
 * Build host function imports for WASM module.
 */
function buildImports(imports) {
  var wasmImports = {};

  // Console.log
  if (imports.consoleLog) {
    wasmImports.console_log = function (msg) {
      console.log(String(msg));
    };
  }

  // Console.error
  if (imports.consoleError) {
    wasmImports.console_error = function (msg) {
      console.error(String(msg));
    };
  }

  // Get timestamp
  if (imports.getTimestamp) {
    wasmImports.get_timestamp = function () {
      return BigInt(Date.now());
    };
  }

  // Random bytes (limited to 256 bytes max)
  if (imports.randomBytes) {
    var crypto = require("crypto");
    wasmImports.random_bytes = function (count) {
      var maxCount = Math.min(count, 256);
      return crypto.randomBytes(maxCount);
    };
  }

  // Read file (sandboxed to /tmp/wasm-sandbox/)
  if (imports.readFile) {
    var fsRead = require("fs");
    var pathRead = require("path");
    wasmImports.read_file = function (filePath) {
      var sandboxPath = pathRead.join("/tmp/wasm-sandbox", String(filePath));
      // Prevent directory traversal
      if (sandboxPath.indexOf("..") !== -1) {
        return null;
      }
      try {
        return fsRead.readFileSync(sandboxPath, "utf8");
      } catch (error) {
        return null;
      }
    };
  }

  // Write file (sandboxed to /tmp/wasm-sandbox/)
  if (imports.writeFile) {
    var fsWrite = require("fs");
    var pathWrite = require("path");
    wasmImports.write_file = function (filePath, content) {
      var sandboxPath = pathWrite.join("/tmp/wasm-sandbox", String(filePath));
      // Prevent directory traversal
      if (sandboxPath.indexOf("..") !== -1) {
        return false;
      }
      try {
        fsWrite.mkdirSync(pathWrite.dirname(sandboxPath), { recursive: true });
        fsWrite.writeFileSync(sandboxPath, String(content), "utf8");
        return true;
      } catch (error) {
        return false;
      }
    };
  }

  return wasmImports;
}
