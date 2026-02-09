// FFI bindings for Tool.Lsp PureScript module
// Implements LSP operations via connected language server clients

import { existsSync } from "fs";

// LSP client registry - populated by the LSP module when servers connect
// Key: language ID, Value: { send: (method, params) => Promise<result> }
const lspClients = new Map();

// Register an LSP client for a language
export function registerLspClient(languageId, client) {
  lspClients.set(languageId, client);
}

// Store for diagnostics (updated by LSP servers)
if (typeof globalThis !== "undefined") {
  globalThis.__forgeLspDiagnostics = globalThis.__forgeLspDiagnostics || new Map();
}

// Check if file exists
export const fileExistsFFI = (filePath) => () => {
  return Promise.resolve(existsSync(filePath));
};

// Determine language from file extension
function getLanguageId(filePath) {
  const ext = filePath.split(".").pop().toLowerCase();
  const mapping = {
    ts: "typescript", tsx: "typescriptreact",
    js: "javascript", jsx: "javascriptreact",
    py: "python", rs: "rust", go: "go",
    hs: "haskell", purs: "purescript",
    lean: "lean4", nix: "nix",
    rb: "ruby", java: "java",
    cpp: "cpp", c: "c", h: "c",
    cs: "csharp", lua: "lua",
    json: "json", yaml: "yaml", yml: "yaml",
    md: "markdown", html: "html", css: "css",
  };
  return mapping[ext] || ext;
}

// Call LSP operation
// Returns Either String (Array Json) via { tag: "Left", value: err } or { tag: "Right", value: results }
export const callLspOperationFFI = (operation) => (filePath) => (position) => () => {
  return new Promise(async (resolve) => {
    try {
      const languageId = getLanguageId(filePath);
      const client = lspClients.get(languageId);

      if (!client) {
        // No LSP client for this language - return empty results
        resolve({ tag: "Right", value: [] });
        return;
      }

      const uri = "file://" + filePath;

      // Map operation to LSP method
      let method;
      let params;

      switch (operation) {
        case "definition":
        case "goto-definition":
          method = "textDocument/definition";
          params = {
            textDocument: { uri },
            position: { line: position.line || 0, character: position.character || 0 }
          };
          break;

        case "references":
        case "find-references":
          method = "textDocument/references";
          params = {
            textDocument: { uri },
            position: { line: position.line || 0, character: position.character || 0 },
            context: { includeDeclaration: true }
          };
          break;

        case "hover":
          method = "textDocument/hover";
          params = {
            textDocument: { uri },
            position: { line: position.line || 0, character: position.character || 0 }
          };
          break;

        case "completion":
          method = "textDocument/completion";
          params = {
            textDocument: { uri },
            position: { line: position.line || 0, character: position.character || 0 }
          };
          break;

        case "diagnostics":
          // Return cached diagnostics
          if (globalThis.__forgeLspDiagnostics) {
            const diags = globalThis.__forgeLspDiagnostics.get(uri) || [];
            resolve({ tag: "Right", value: diags });
          } else {
            resolve({ tag: "Right", value: [] });
          }
          return;

        case "symbols":
        case "document-symbols":
          method = "textDocument/documentSymbol";
          params = { textDocument: { uri } };
          break;

        default:
          resolve({ tag: "Left", value: "Unknown LSP operation: " + operation });
          return;
      }

      // Send request to LSP server
      const result = await client.send(method, params);
      resolve({ tag: "Right", value: Array.isArray(result) ? result : [result] });
    } catch (e) {
      resolve({
        tag: "Left",
        value: "LSP operation failed: " + e.message
      });
    }
  });
};
