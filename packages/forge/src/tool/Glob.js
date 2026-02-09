// FFI bindings for Tool.Glob PureScript module

import { spawn } from "child_process";

// Execute ripgrep --files command
export const executeRgFilesFFI = (args) => (searchPath) => () => {
  return new Promise((resolve) => {
    try {
      const rg = spawn("rg", args, {
        cwd: searchPath,
        timeout: 30000,
        maxBuffer: 10 * 1024 * 1024 // 10MB
      });
      
      let stdout = "";
      let stderr = "";
      
      rg.stdout.on("data", (data) => {
        stdout += data.toString();
      });
      
      rg.stderr.on("data", (data) => {
        stderr += data.toString();
      });
      
      rg.on("close", (code) => {
        // Exit code 1 means no matches, which is not an error for glob
        if (code === 0 || code === 1) {
          resolve({ tag: "Right", value: stdout });
        } else {
          resolve({ tag: "Left", value: `ripgrep error (code ${code}): ${stderr}` });
        }
      });
      
      rg.on("error", (err) => {
        resolve({
          tag: "Left",
          value: `Failed to execute ripgrep: ${err.message}`
        });
      });
    } catch (e) {
      resolve({
        tag: "Left",
        value: `ripgrep error: ${e.message}`
      });
    }
  });
};
