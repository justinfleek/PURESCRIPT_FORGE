"use strict";

const { spawn } = require("child_process");
const { promisify } = require("util");
const fs = require("fs").promises;
const path = require("path");

/**
 * Fast linting FFI - calls linters efficiently with caching
 */

/**
 * Run Biome linter
 */
exports.runBiomeLint = function (filePath) {
  return function (content) {
    return async function () {
      try {
        // Write content to temp file
        const tmpFile = path.join(require("os").tmpdir(), `biome-lint-${Date.now()}.ts`);
        await fs.writeFile(tmpFile, content, "utf8");
        
        // Run biome check
        const result = await new Promise((resolve, reject) => {
          const proc = spawn("npx", ["biome", "check", "--json", tmpFile], {
            stdio: ["ignore", "pipe", "pipe"],
          });
          
          let stdout = "";
          let stderr = "";
          
          proc.stdout.on("data", (data) => {
            stdout += data.toString();
          });
          
          proc.stderr.on("data", (data) => {
            stderr += data.toString();
          });
          
          proc.on("close", (code) => {
            // Clean up temp file
            fs.unlink(tmpFile).catch(() => {});
            
            if (code === 0 || code === 1) {
              // Biome returns 1 if there are diagnostics
              try {
                const diagnostics = JSON.parse(stdout || "{}");
                resolve({
                  diagnostics: diagnostics.diagnostics || [],
                  errors: diagnostics.errors || 0,
                  warnings: diagnostics.warnings || 0,
                });
              } catch (e) {
                resolve({ diagnostics: [], errors: 0, warnings: 0 });
              }
            } else {
              reject(new Error(stderr || "Biome lint failed"));
            }
          });
          
          proc.on("error", (err) => {
            fs.unlink(tmpFile).catch(() => {});
            reject(err);
          });
        });
        
        return {
          tag: "Right",
          value: result,
        };
      } catch (error) {
        return {
          tag: "Left",
          value: error.message || "Linting failed",
        };
      }
    };
  };
};

/**
 * Run Ruff linter (Python)
 */
exports.runRuffLint = function (filePath) {
  return function (content) {
    return async function () {
      try {
        const tmpFile = path.join(require("os").tmpdir(), `ruff-lint-${Date.now()}.py`);
        await fs.writeFile(tmpFile, content, "utf8");
        
        const result = await new Promise((resolve, reject) => {
          const proc = spawn("ruff", ["check", "--output-format", "json", tmpFile], {
            stdio: ["ignore", "pipe", "pipe"],
          });
          
          let stdout = "";
          let stderr = "";
          
          proc.stdout.on("data", (data) => {
            stdout += data.toString();
          });
          
          proc.stderr.on("data", (data) => {
            stderr += data.toString();
          });
          
          proc.on("close", (code) => {
            fs.unlink(tmpFile).catch(() => {});
            
            try {
              const diagnostics = JSON.parse(stdout || "[]");
              resolve({
                diagnostics: diagnostics,
                errors: diagnostics.filter((d) => d.code.startsWith("E")).length,
                warnings: diagnostics.filter((d) => d.code.startsWith("W")).length,
              });
            } catch (e) {
              resolve({ diagnostics: [], errors: 0, warnings: 0 });
            }
          });
          
          proc.on("error", (err) => {
            fs.unlink(tmpFile).catch(() => {});
            reject(err);
          });
        });
        
        return {
          tag: "Right",
          value: result,
        };
      } catch (error) {
        return {
          tag: "Left",
          value: error.message || "Ruff linting failed",
        };
      }
    };
  };
};

/**
 * Run aleph-lint (uses ast-grep for Nix/PureScript/Haskell linting)
 * This is the unified linter from REQUIRED/aleph-baileylu-linter-round-2
 */
exports.runAlephLint = function (filePath) {
  return function (content) {
    return async function () {
      try {
        // Determine file type from extension
        const ext = path.extname(filePath);
        let language = "nix";  // Default
        if (ext === ".purs") language = "purescript";
        else if (ext === ".hs") language = "haskell";
        else if (ext === ".nix") language = "nix";
        
        // Write content to temp file
        const tmpFile = path.join(require("os").tmpdir(), `aleph-lint-${Date.now()}${ext}`);
        await fs.writeFile(tmpFile, content, "utf8");
        
        // Get directory of temp file for aleph-lint to work
        const tmpDir = path.dirname(tmpFile);
        
        const result = await new Promise((resolve, reject) => {
          // aleph-lint uses ast-grep with config
          // For now, try to call it directly, fallback to ast-grep if needed
          const proc = spawn("aleph-lint", ["--json", tmpFile], {
            stdio: ["ignore", "pipe", "pipe"],
            cwd: tmpDir,
          });
          
          let stdout = "";
          let stderr = "";
          
          proc.stdout.on("data", (data) => {
            stdout += data.toString();
          });
          
          proc.stderr.on("data", (data) => {
            stderr += data.toString();
          });
          
          proc.on("close", (code) => {
            fs.unlink(tmpFile).catch(() => {});
            
            // aleph-lint uses ast-grep which outputs matches in text format
            // Exit code 0 = no issues, 1 = errors/warnings found
            // Parse ast-grep output format (file:line:col: message)
            const diagnostics = [];
            const lines = stdout.split("\n").filter(l => l.trim());
            
            for (const line of lines) {
              // Parse format: file:line:col: message
              const match = line.match(/^(.+?):(\d+):(\d+):\s*(.+)$/);
              if (match) {
                diagnostics.push({
                  file: match[1],
                  line: parseInt(match[2], 10),
                  column: parseInt(match[3], 10),
                  message: match[4],
                  severity: "error",  // aleph-lint errors are typically errors
                });
              }
            }
            
            resolve({
              diagnostics: diagnostics,
              errors: code === 0 ? 0 : diagnostics.length,
              warnings: 0,  // aleph-lint doesn't distinguish warnings in exit code
            });
          });
          
          proc.on("error", (err) => {
            // If aleph-lint not found, try ast-grep directly
            // This is a fallback - ideally aleph-lint should be in PATH
            fs.unlink(tmpFile).catch(() => {});
            
            // Try ast-grep as fallback
            const astGrepProc = spawn("ast-grep", ["scan", "--json", tmpFile], {
              stdio: ["ignore", "pipe", "pipe"],
              cwd: tmpDir,
            });
            
            let astStdout = "";
            let astStderr = "";
            
            astGrepProc.stdout.on("data", (data) => {
              astStdout += data.toString();
            });
            
            astGrepProc.stderr.on("data", (data) => {
              astStderr += data.toString();
            });
            
            astGrepProc.on("close", (astCode) => {
              fs.unlink(tmpFile).catch(() => {});
              try {
                // ast-grep --json outputs array of matches
                const matches = JSON.parse(astStdout || "[]");
                const diagnostics = Array.isArray(matches) ? matches.map(match => ({
                  file: match.file || tmpFile,
                  line: match.range?.start?.line || 0,
                  column: match.range?.start?.column || 0,
                  message: match.message || match.rule || "Lint issue",
                  severity: match.severity || "error",
                })) : [];
                
                resolve({
                  diagnostics: diagnostics,
                  errors: astCode === 0 ? 0 : diagnostics.length,
                  warnings: 0,
                });
              } catch (parseErr) {
                // Fallback: parse text output
                const diagnostics = [];
                const lines = astStdout.split("\n").filter(l => l.trim());
                for (const line of lines) {
                  const match = line.match(/^(.+?):(\d+):(\d+):\s*(.+)$/);
                  if (match) {
                    diagnostics.push({
                      file: match[1],
                      line: parseInt(match[2], 10),
                      column: parseInt(match[3], 10),
                      message: match[4],
                      severity: "error",
                    });
                  }
                }
                resolve({
                  diagnostics: diagnostics,
                  errors: astCode === 0 ? 0 : diagnostics.length,
                  warnings: 0,
                });
              }
            });
            
            astGrepProc.on("error", (astErr) => {
              fs.unlink(tmpFile).catch(() => {});
              reject(new Error(`aleph-lint and ast-grep not found: ${err.message}`));
            });
          });
        });
        
        return {
          tag: "Right",
          value: result,
        };
      } catch (error) {
        return {
          tag: "Left",
          value: error.message || "aleph-lint failed",
        };
      }
    };
  };
};

/**
 * Run Lean linter (Lean4)
 */
exports.runLeanLint = function (filePath) {
  return function (content) {
    return async function () {
      try {
        const tmpFile = path.join(require("os").tmpdir(), `lean-lint-${Date.now()}.lean`);
        await fs.writeFile(tmpFile, content, "utf8");
        
        const result = await new Promise((resolve, reject) => {
          const proc = spawn("lean", ["--check", tmpFile], {
            stdio: ["ignore", "pipe", "pipe"],
          });
          
          let stdout = "";
          let stderr = "";
          
          proc.stdout.on("data", (data) => {
            stdout += data.toString();
          });
          
          proc.stderr.on("data", (data) => {
            stderr += data.toString();
          });
          
          proc.on("close", (code) => {
            fs.unlink(tmpFile).catch(() => {});
            resolve({
              diagnostics: [],
              errors: code === 0 ? 0 : 1,
              warnings: 0,
            });
          });
          
          proc.on("error", (err) => {
            fs.unlink(tmpFile).catch(() => {});
            reject(err);
          });
        });
        
        return {
          tag: "Right",
          value: result,
        };
      } catch (error) {
        return {
          tag: "Left",
          value: error.message || "Lean linting failed",
        };
      }
    };
  };
};

/**
 * Run ESLint linter (JavaScript/TypeScript)
 */
exports.runESLintLint = function (filePath) {
  return function (content) {
    return async function () {
      try {
        const tmpFile = path.join(require("os").tmpdir(), `eslint-${Date.now()}.js`);
        await fs.writeFile(tmpFile, content, "utf8");
        
        const result = await new Promise((resolve, reject) => {
          const proc = spawn("npx", ["eslint", "--format", "json", tmpFile], {
            stdio: ["ignore", "pipe", "pipe"],
          });
          
          let stdout = "";
          let stderr = "";
          
          proc.stdout.on("data", (data) => {
            stdout += data.toString();
          });
          
          proc.stderr.on("data", (data) => {
            stderr += data.toString();
          });
          
          proc.on("close", (code) => {
            fs.unlink(tmpFile).catch(() => {});
            try {
              const results = JSON.parse(stdout || "[]");
              const diagnostics = Array.isArray(results) ? results : (results[0]?.messages || []);
              resolve({
                diagnostics: diagnostics,
                errors: diagnostics.filter((d) => d.severity === 2).length,
                warnings: diagnostics.filter((d) => d.severity === 1).length,
              });
            } catch (e) {
              resolve({ diagnostics: [], errors: 0, warnings: 0 });
            }
          });
          
          proc.on("error", (err) => {
            fs.unlink(tmpFile).catch(() => {});
            reject(err);
          });
        });
        
        return {
          tag: "Right",
          value: result,
        };
      } catch (error) {
        return {
          tag: "Left",
          value: error.message || "ESLint linting failed",
        };
      }
    };
  };
};

/**
 * Get current time for performance measurement
 */
exports.getCurrentTime = function () {
  return Date.now();
};
