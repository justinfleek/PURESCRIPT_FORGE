"use strict";

const { spawn } = require("child_process");
const net = require("net");
const { Readable, Writable } = require("stream");

/**
 * LSP Client FFI - Language Server Protocol communication
 * Implements JSON-RPC 2.0 over stdio/TCP/WebSocket
 */

// LSP message format: Content-Length: <length>\r\n\r\n<json>
function formatLSPMessage(json) {
  const content = JSON.stringify(json);
  const length = Buffer.byteLength(content, "utf8");
  return `Content-Length: ${length}\r\n\r\n${content}`;
}

// Parse LSP message header
function parseLSPHeader(buffer) {
  const headerEnd = buffer.indexOf("\r\n\r\n");
  if (headerEnd === -1) return null;
  
  const header = buffer.toString("utf8", 0, headerEnd);
  const match = header.match(/Content-Length:\s*(\d+)/i);
  if (!match) return null;
  
  return {
    contentLength: parseInt(match[1], 10),
    headerLength: headerEnd + 4
  };
}

// LSP Connection Manager
class LSPConnection {
  constructor(process, stdin, stdout, stderr) {
    this.process = process;
    this.stdin = stdin;
    this.stdout = stdout;
    this.stderr = stderr;
    this.requestId = 1;
    this.pendingRequests = new Map();
    this.buffer = Buffer.alloc(0);
    this.isInitialized = false;
    this.capabilities = null;
    
    // Set up message reader
    this.setupMessageReader();
  }
  
  setupMessageReader() {
    this.stdout.on("data", (chunk) => {
      this.buffer = Buffer.concat([this.buffer, chunk]);
      this.processMessages();
    });
    
    this.stderr.on("data", (chunk) => {
      // Log stderr for debugging
      console.error("[LSP stderr]", chunk.toString());
    });
    
    this.process.on("exit", (code) => {
      // Clean up pending requests
      for (const [id, resolve] of this.pendingRequests) {
        resolve({ tag: "Left", value: `LSP server exited with code ${code}` });
      }
      this.pendingRequests.clear();
    });
  }
  
  processMessages() {
    while (true) {
      const headerInfo = parseLSPHeader(this.buffer);
      if (!headerInfo) break;
      
      const totalLength = headerInfo.headerLength + headerInfo.contentLength;
      if (this.buffer.length < totalLength) break;
      
      const content = this.buffer.toString("utf8", headerInfo.headerLength, totalLength);
      this.buffer = this.buffer.slice(totalLength);
      
      try {
        const message = JSON.parse(content);
        this.handleMessage(message);
      } catch (error) {
        console.error("[LSP] Failed to parse message:", error);
      }
    }
  }
  
  handleMessage(message) {
    // Handle responses
    if (message.id !== undefined && this.pendingRequests.has(message.id)) {
      const resolve = this.pendingRequests.get(message.id);
      this.pendingRequests.delete(message.id);
      
      if (message.error) {
        resolve({ tag: "Left", value: message.error.message || "LSP error" });
      } else {
        resolve({ tag: "Right", value: message.result || null });
      }
      return;
    }
    
    // Handle notifications (e.g., window/logMessage)
    if (message.method) {
      // Could handle server notifications here
      if (message.method === "window/logMessage") {
        console.log("[LSP]", message.params);
      }
    }
  }
  
  sendRequest(method, params) {
    return new Promise((resolve) => {
      const id = this.requestId++;
      const request = {
        jsonrpc: "2.0",
        id: id,
        method: method,
        params: params || {}
      };
      
      this.pendingRequests.set(id, resolve);
      const message = formatLSPMessage(request);
      this.stdin.write(message, "utf8");
    });
  }
  
  sendNotification(method, params) {
    const notification = {
      jsonrpc: "2.0",
      method: method,
      params: params || {}
    };
    const message = formatLSPMessage(notification);
    this.stdin.write(message, "utf8");
  }
  
  async initialize(rootUri, capabilities) {
    const result = await this.sendRequest("initialize", {
      processId: this.process.pid,
      rootUri: rootUri,
      capabilities: capabilities || {},
      workspaceFolders: null
    });
    
    if (result.tag === "Right" && result.value) {
      this.capabilities = result.value.capabilities || {};
      this.isInitialized = true;
      
      // Send initialized notification
      this.sendNotification("initialized", {});
    }
    
    return result;
  }
  
  disconnect() {
    this.sendNotification("shutdown", {});
    this.process.kill();
  }
}

/**
 * Connect to LSP server via stdio
 */
exports.connectLSPStdio = function (command) {
  return function (args) {
    return function () {
      return new Promise((resolve) => {
        try {
          const proc = spawn(command, args, {
            stdio: ["pipe", "pipe", "pipe"],
          });
          
          const connection = new LSPConnection(proc, proc.stdin, proc.stdout, proc.stderr);
          
          resolve({
            tag: "Right",
            value: connection,
          });
        } catch (error) {
          resolve({
            tag: "Left",
            value: error.message,
          });
        }
      });
    };
  };
};

/**
 * Connect to LSP server via TCP socket
 */
exports.connectLSPTcp = function (host) {
  return function (port) {
    return function () {
      return new Promise((resolve, reject) => {
        try {
          const socket = net.createConnection(port, host, () => {
            resolve({
              tag: "Right",
              value: socket,
            });
          });
          
          socket.on("error", (error) => {
            resolve({
              tag: "Left",
              value: error.message,
            });
          });
        } catch (error) {
          resolve({
            tag: "Left",
            value: error.message,
          });
        }
      });
    };
  };
};

/**
 * Connect to LSP server (uses stdio connection)
 */
exports.connectLSPFFI = function (language) {
  return function (serverConfig) {
    return async function () {
      try {
        // Parse server config: { command: String, args: Array String, rootUri: String }
        const config = typeof serverConfig === "string" 
          ? JSON.parse(serverConfig)
          : serverConfig;
        
        const command = config.command || getDefaultCommand(language);
        const args = config.args || getDefaultArgs(language);
        
        const connectionResult = await exports.connectLSPStdio(command)(args)();
        
        if (connectionResult.tag === "Left") {
          return connectionResult;
        }
        
        const connection = connectionResult.value;
        
        // Initialize LSP connection
        const rootUri = config.rootUri || "file:///";
        const initResult = await connection.initialize(rootUri, {
          textDocument: {
            hover: { dynamicRegistration: true },
            definition: { dynamicRegistration: true },
            references: { dynamicRegistration: true },
            documentSymbol: { dynamicRegistration: true },
            signatureHelp: { dynamicRegistration: true }
          }
        });
        
        if (initResult.tag === "Left") {
          connection.disconnect();
          return initResult;
        }
        
        const capabilities = connection.capabilities || {};
        
        return {
          tag: "Right",
          value: {
            connection: connection,
            isConnected: true,
            capabilities: {
              hover: !!(capabilities.hoverProvider),
              definition: !!(capabilities.definitionProvider),
              references: !!(capabilities.referencesProvider),
              completion: !!(capabilities.completionProvider),
              signatureHelp: !!(capabilities.signatureHelpProvider),
              documentSymbol: !!(capabilities.documentSymbolProvider),
            },
          },
        };
      } catch (error) {
        return {
          tag: "Left",
          value: error.message || "LSP connection failed",
        };
      }
    };
  };
};

// Get default LSP server command for language
function getDefaultCommand(language) {
  const commands = {
    "typescript": "typescript-language-server",
    "javascript": "typescript-language-server",
    "purescript": "purescript-language-server",
    "haskell": "haskell-language-server-wrapper",
    "lean4": "lean",
    "python": "pylsp",
  };
  return commands[language] || "echo";
}

// Get default args for language server
function getDefaultArgs(language) {
  const args = {
    "typescript": ["--stdio"],
    "javascript": ["--stdio"],
    "purescript": ["--stdio"],
    "haskell": ["--lsp"],
    "lean4": ["--server"],
    "python": [],
  };
  return args[language] || [];
}

/**
 * Hover at position
 */
exports.hoverLSPFFI = function (connection) {
  return function (fileUri) {
    return function (position) {
      return async function () {
        try {
          // Ensure document is open
          await connection.sendNotification("textDocument/didOpen", {
            textDocument: {
              uri: fileUri,
              languageId: detectLanguageFromUri(fileUri),
              version: 1,
              text: "" // Would get actual content
            }
          });
          
          const result = await connection.sendRequest("textDocument/hover", {
            textDocument: { uri: fileUri },
            position: { line: position.line, character: position.column }
          });
          
          if (result.tag === "Left") {
            return null;
          }
          
          const hover = result.value;
          if (!hover || !hover.contents) {
            return null;
          }
          
          // Extract hover information
          const contents = Array.isArray(hover.contents) 
            ? hover.contents 
            : [hover.contents];
          
          let name = "";
          let type_ = "";
          let documentation = "";
          
          contents.forEach((content) => {
            if (typeof content === "string") {
              type_ += content + "\n";
            } else if (content.value) {
              type_ += content.value + "\n";
            }
          });
          
          return {
            name: name || "symbol",
            type_: type_.trim() || null,
            documentation: documentation || null,
            range: hover.range || null
          };
        } catch (error) {
          return null;
        }
      };
    };
  };
};

/**
 * Go to definition
 */
exports.definitionLSPFFI = function (connection) {
  return function (fileUri) {
    return function (position) {
      return async function () {
        try {
          const result = await connection.sendRequest("textDocument/definition", {
            textDocument: { uri: fileUri },
            position: { line: position.line, character: position.column }
          });
          
          if (result.tag === "Left" || !result.value) {
            return null;
          }
          
          const definition = Array.isArray(result.value) 
            ? result.value[0] 
            : result.value;
          
          if (!definition || !definition.uri) {
            return null;
          }
          
          return {
            uri: definition.uri,
            range: definition.range || {
              start: { line: 0, column: 0 },
              end: { line: 0, column: 0 }
            }
          };
        } catch (error) {
          return null;
        }
      };
    };
  };
};

/**
 * Find references
 */
exports.referencesLSPFFI = function (connection) {
  return function (fileUri) {
    return function (position) {
      return async function () {
        try {
          const result = await connection.sendRequest("textDocument/references", {
            textDocument: { uri: fileUri },
            position: { line: position.line, character: position.column },
            context: { includeDeclaration: true }
          });
          
          if (result.tag === "Left" || !result.value) {
            return [];
          }
          
          return result.value.map((ref) => ({
            uri: ref.uri,
            range: ref.range
          }));
        } catch (error) {
          return [];
        }
      };
    };
  };
};

/**
 * Get document symbols
 */
exports.documentSymbolsLSPFFI = function (connection) {
  return function (fileUri) {
    return async function () {
      try {
        const result = await connection.sendRequest("textDocument/documentSymbol", {
          textDocument: { uri: fileUri }
        });
        
        if (result.tag === "Left" || !result.value) {
          return [];
        }
        
        return result.value.map((symbol) => ({
          name: symbol.name || "",
          kind: symbolKindFromLSP(symbol.kind),
          definition: {
            uri: fileUri,
            range: symbol.range || symbol.location?.range || {
              start: { line: 0, column: 0 },
              end: { line: 0, column: 0 }
            }
          },
          type_: symbol.detail || null,
          documentation: extractDocumentation(symbol),
          containerName: symbol.containerName || null
        }));
      } catch (error) {
        return [];
      }
    };
  };
};

/**
 * Get signature help
 */
exports.signatureHelpLSPFFI = function (connection) {
  return function (fileUri) {
    return function (position) {
      return async function () {
        try {
          const result = await connection.sendRequest("textDocument/signatureHelp", {
            textDocument: { uri: fileUri },
            position: { line: position.line, character: position.column }
          });
          
          if (result.tag === "Left" || !result.value) {
            return null;
          }
          
          const help = result.value;
          return {
            signatures: (help.signatures || []).map((sig) => ({
              label: sig.label || "",
              documentation: extractDocumentation(sig),
              parameters: (sig.parameters || []).map((param) => ({
                label: typeof param === "string" ? param : param.label || "",
                documentation: extractDocumentation(param)
              }))
            })),
            activeSignature: help.activeSignature || 0,
            activeParameter: help.activeParameter || 0
          };
        } catch (error) {
          return null;
        }
      };
    };
  };
};

// Helper functions
function detectLanguageFromUri(uri) {
  if (uri.endsWith(".ts")) return "typescript";
  if (uri.endsWith(".js")) return "javascript";
  if (uri.endsWith(".purs")) return "purescript";
  if (uri.endsWith(".hs")) return "haskell";
  if (uri.endsWith(".lean")) return "lean";
  if (uri.endsWith(".py")) return "python";
  return "plaintext";
}

function symbolKindFromLSP(kind) {
  // LSP SymbolKind enum values
  const kinds = {
    1: "File", 2: "Module", 3: "Namespace", 4: "Package",
    5: "Class", 6: "Method", 7: "Property", 8: "Field",
    9: "Constructor", 10: "Enum", 11: "Interface", 12: "Function",
    13: "Variable", 14: "Constant", 15: "String", 16: "Number",
    17: "Boolean", 18: "Array", 19: "Object", 20: "Key",
    21: "Null", 22: "EnumMember", 23: "Struct", 24: "Event",
    25: "Operator", 26: "TypeParameter"
  };
  return kinds[kind] || "Variable";
}

function extractDocumentation(obj) {
  if (obj.documentation) {
    if (typeof obj.documentation === "string") {
      return obj.documentation;
    } else if (obj.documentation.value) {
      return obj.documentation.value;
    }
  }
  return null;
}

/**
 * Notify document opened
 */
exports.notifyDocumentDidOpenFFI = function (connection) {
  return function (fileUri) {
    return function (languageId) {
      return function (content) {
        return function () {
          return new Promise((resolve) => {
            try {
              connection.sendNotification("textDocument/didOpen", {
                textDocument: {
                  uri: fileUri,
                  languageId: languageId,
                  version: 1,
                  text: content
                }
              });
              resolve();
            } catch (error) {
              resolve();
            }
          });
        };
      };
    };
  };
};

/**
 * Notify document changed
 */
exports.notifyDocumentDidChangeFFI = function (connection) {
  return function (fileUri) {
    return function (content) {
      return function () {
        return new Promise((resolve) => {
          try {
            connection.sendNotification("textDocument/didChange", {
              textDocument: {
                uri: fileUri,
                version: Date.now() // Simple versioning
              },
              contentChanges: [{
                text: content
              }]
            });
            resolve();
          } catch (error) {
            resolve();
          }
        });
      };
    };
  };
};

/**
 * Notify document closed
 */
exports.notifyDocumentDidCloseFFI = function (connection) {
  return function (fileUri) {
    return function () {
      return new Promise((resolve) => {
        try {
          connection.sendNotification("textDocument/didClose", {
            textDocument: {
              uri: fileUri
            }
          });
          resolve();
        } catch (error) {
          resolve();
        }
      });
    };
  };
};

/**
 * Disconnect from LSP server
 */
exports.disconnectLSPFFI = function (connection) {
  return function () {
    return new Promise((resolve) => {
      try {
        connection.disconnect();
        resolve();
      } catch (error) {
        resolve();
      }
    });
  };
};
