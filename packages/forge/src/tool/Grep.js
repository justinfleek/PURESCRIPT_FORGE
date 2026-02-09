// FFI bindings for Tool.Grep PureScript module

import { spawn } from "child_process";

// Execute ripgrep command
export const executeRgFFI = (args) => (searchPath) => () => {
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
        resolve({
          tag: "Right",
          value: {
            output: stdout,
            exitCode: code ?? 0
          }
        });
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

// Validate regex pattern
export const validateRegexFFI = (pattern) => {
  try {
    new RegExp(pattern);
    return { tag: "Right", value: undefined };
  } catch (e) {
    return { tag: "Left", value: `Invalid regex: ${e.message}` };
  }
};
