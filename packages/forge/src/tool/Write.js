// FFI bindings for Tool.Write PureScript module

import { existsSync, writeFileSync, mkdirSync } from "fs";
import { dirname } from "path";

// Check if file exists
export const checkFileExistsFFI = (filePath) => () => {
  return Promise.resolve({
    tag: "Right",
    value: existsSync(filePath)
  });
};

// Write file content
export const writeFileFFI = (filePath) => (content) => () => {
  return new Promise((resolve) => {
    try {
      // Ensure directory exists
      const dir = dirname(filePath);
      if (!existsSync(dir)) {
        mkdirSync(dir, { recursive: true });
      }
      
      writeFileSync(filePath, content, "utf-8");
      resolve({ tag: "Right", value: undefined });
    } catch (e) {
      resolve({ tag: "Left", value: `Failed to write file: ${e.message}` });
    }
  });
};

// Notify LSP of file change
// Emits textDocument/didSave notification via event bus
export const notifyLspFFI = (filePath) => () => {
  return new Promise((resolve) => {
    try {
      // Emit file change event for any LSP client listeners
      // The LSP module subscribes to these events and forwards to language servers
      if (typeof process !== "undefined" && process.emit) {
        process.emit("forge:file-changed", {
          type: "didSave",
          uri: "file://" + filePath,
          timestamp: Date.now()
        });
      }
      resolve(undefined);
    } catch (e) {
      // Non-critical: LSP notification failure should not block writes
      resolve(undefined);
    }
  });
};

// Get diagnostics from LSP
// Returns array of diagnostic objects from any connected LSP servers
export const getDiagnosticsFFI = (filePath) => () => {
  return new Promise((resolve) => {
    try {
      // Check for diagnostics store (populated by LSP module)
      if (typeof globalThis !== "undefined" && globalThis.__forgeLspDiagnostics) {
        const uri = "file://" + filePath;
        const diagnostics = globalThis.__forgeLspDiagnostics.get(uri) || [];
        resolve(diagnostics.map(d => ({
          range: {
            start: { line: d.range.start.line, character: d.range.start.character },
            end: { line: d.range.end.line, character: d.range.end.character }
          },
          severity: d.severity || 1,
          message: d.message || "",
          source: d.source || ""
        })));
      } else {
        resolve([]);
      }
    } catch (e) {
      resolve([]);
    }
  });
};
