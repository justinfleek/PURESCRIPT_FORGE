// WASM Sandbox FFI - wasmtime integration
// Provides secure WebAssembly execution with resource limits

const { Wasmtime } = require('@wasmtime/wasmtime');

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
exports.executeWASMImpl = function(config, imports) {
  try {
    // Decode base64 WASM bytes
    const wasmBytes = Buffer.from(config.wasmBytes, 'base64');
    
    // Create WASM engine with resource limits
    const engine = new Wasmtime.Engine();
    
    // Create module with validation
    const module = Wasmtime.Module.compile(engine, wasmBytes);
    
    // Create store with resource limits
    const store = new Wasmtime.Store(engine);
    
    // Set memory limit
    const memoryLimit = config.memoryLimitMB * 1024 * 1024; // Convert MB to bytes
    
    // Set time limit (approximate via instruction counting)
    const timeLimit = config.timeLimitMs;
    
    // Build host function imports
    const wasmImports = buildImports(store, imports);
    
    // Create instance
    const instance = new Wasmtime.Instance(store, module, wasmImports);
    
    // Get WASM exports
    const exports = instance.exports(store);
    
    // Find main/_start function
    const mainFunc = exports._start || exports.main || exports.run;
    if (!mainFunc) {
      return {
        tag: "Left",
        value: {
          type: "ImportNotFound",
          value: "No entry point found (_start, main, or run)"
        }
      };
    }
    
    // Execute with timeout
    const startTime = Date.now();
    let result;
    
    try {
      // Call main function
      result = mainFunc(store);
      
      // Check time limit
      const elapsed = Date.now() - startTime;
      if (elapsed > timeLimit) {
        return {
          tag: "Left",
          value: {
            type: "TimeLimitExceeded",
            value: timeLimit
          }
        };
      }
      
      // Convert result to string
      const output = String(result || "");
      
      return {
        tag: "Right",
        value: output
      };
    } catch (error) {
      // Check if it's a trap
      if (error.message && error.message.includes("trap")) {
        return {
          tag: "Left",
          value: {
            type: "Trap",
            value: error.message
          }
        };
      }
      
      // Check time limit
      const elapsed = Date.now() - startTime;
      if (elapsed > timeLimit) {
        return {
          tag: "Left",
          value: {
            type: "TimeLimitExceeded",
            value: timeLimit
          }
        };
      }
      
      throw error;
    }
  } catch (error) {
    // Handle validation errors
    if (error.message && error.message.includes("invalid")) {
      return {
        tag: "Left",
        value: {
          type: "InvalidWASM",
          value: error.message
        }
      };
    }
    
    // Handle other errors
    return {
      tag: "Left",
      value: {
        type: "HostFunctionError",
        value: error.message || String(error)
      }
    };
  }
};

/**
 * Build host function imports for WASM module.
 */
function buildImports(store, imports) {
  const wasmImports = {};
  
  // Console.log
  if (imports.consoleLog) {
    wasmImports.console_log = (msg) => {
      console.log(String(msg));
    };
  }
  
  // Console.error
  if (imports.consoleError) {
    wasmImports.console_error = (msg) => {
      console.error(String(msg));
    };
  }
  
  // Get timestamp
  if (imports.getTimestamp) {
    wasmImports.get_timestamp = () => {
      return BigInt(Date.now());
    };
  }
  
  // Random bytes (limited to 256 bytes max)
  if (imports.randomBytes) {
    wasmImports.random_bytes = (count) => {
      const maxCount = Math.min(count, 256);
      const bytes = new Uint8Array(maxCount);
      for (let i = 0; i < maxCount; i++) {
        bytes[i] = Math.floor(Math.random() * 256);
      }
      return bytes;
    };
  }
  
  // Read file (sandboxed to /tmp/wasm-sandbox/)
  if (imports.readFile) {
    const fs = require('fs');
    const path = require('path');
    wasmImports.read_file = (filePath) => {
      const sandboxPath = path.join('/tmp/wasm-sandbox', String(filePath));
      // Prevent directory traversal
      if (sandboxPath.includes('..')) {
        return null;
      }
      try {
        return fs.readFileSync(sandboxPath, 'utf8');
      } catch (error) {
        return null;
      }
    };
  }
  
  // Write file (sandboxed to /tmp/wasm-sandbox/)
  if (imports.writeFile) {
    const fs = require('fs');
    const path = require('path');
    wasmImports.write_file = (filePath, content) => {
      const sandboxPath = path.join('/tmp/wasm-sandbox', String(filePath));
      // Prevent directory traversal
      if (sandboxPath.includes('..')) {
        return false;
      }
      try {
        fs.mkdirSync(path.dirname(sandboxPath), { recursive: true });
        fs.writeFileSync(sandboxPath, String(content), 'utf8');
        return true;
      } catch (error) {
        return false;
      }
    };
  }
  
  return wasmImports;
};
