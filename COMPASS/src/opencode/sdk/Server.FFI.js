"use strict";

const { spawn } = require("node:child_process");

/**
 * Spawn opencode server process
 */
exports.spawnOpencodeProcess = function (args) {
  return function (signal) {
    return function (config) {
      return function () {
        try {
          const env = { ...process.env };
          if (config) {
            env.OPENCODE_CONFIG_CONTENT = JSON.stringify(config);
          }
          
          const proc = spawn("opencode", args, {
            signal: signal || undefined,
            env: env,
          });
          
          return { tag: "Right", value: proc };
        } catch (error) {
          return { tag: "Left", value: error.message || "Failed to spawn process" };
        }
      };
    };
  };
};

/**
 * Spawn opencode TUI process
 */
exports.spawnOpencodeTuiProcess = function (args) {
  return function (signal) {
    return function (config) {
      return function () {
        try {
          const env = { ...process.env };
          if (config) {
            env.OPENCODE_CONFIG_CONTENT = JSON.stringify(config);
          }
          
          const proc = spawn("opencode", args, {
            signal: signal || undefined,
            stdio: "inherit",
            env: env,
          });
          
          return { tag: "Right", value: proc };
        } catch (error) {
          return { tag: "Left", value: error.message || "Failed to spawn process" };
        }
      };
    };
  };
};

/**
 * Wait for server URL from process output
 */
exports.waitForServerUrlFFI = function (proc) {
  return function (timeout) {
    return function () {
      return new Promise((resolve) => {
        const id = setTimeout(() => {
          resolve({
            tag: "Left",
            value: `Timeout waiting for server to start after ${timeout}ms`,
          });
        }, timeout);
        
        let output = "";
        
        const onData = (chunk) => {
          output += chunk.toString();
          const lines = output.split("\n");
          for (const line of lines) {
            if (line.startsWith("opencode server listening")) {
              const match = line.match(/on\s+(https?:\/\/[^\s]+)/);
              if (match && match[1]) {
                clearTimeout(id);
                proc.stdout?.removeListener("data", onData);
                proc.stderr?.removeListener("data", onData);
                resolve({ tag: "Right", value: match[1] });
                return;
              }
            }
          }
        };
        
        proc.stdout?.on("data", onData);
        proc.stderr?.on("data", onData);
        
        proc.on("exit", (code) => {
          clearTimeout(id);
          let msg = `Server exited with code ${code}`;
          if (output.trim()) {
            msg += `\nServer output: ${output}`;
          }
          resolve({ tag: "Left", value: msg });
        });
        
        proc.on("error", (error) => {
          clearTimeout(id);
          resolve({ tag: "Left", value: error.message || "Process error" });
        });
      });
    };
  };
};
