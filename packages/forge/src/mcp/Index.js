// FFI bindings for Forge.MCP.Index PureScript module
// Implements MCP stdio transport via JSON-RPC over child_process

import { existsSync, readFileSync } from "fs";
import { join } from "path";
import { spawn } from "child_process";

// Active MCP process connections
const connections = new Map();

// JSON-RPC request ID counter
let requestId = 0;

// Load MCP configurations from config file
export const loadMCPConfigsFFI = () => {
  return new Promise((resolve) => {
    try {
      // Try to load from common config locations
      const configPaths = [
        join(process.cwd(), ".opencode", "mcp.json"),
        join(process.cwd(), "opencode.json"),
        join(process.env.HOME || "", ".config", "opencode", "mcp.json")
      ];

      for (const configPath of configPaths) {
        if (existsSync(configPath)) {
          const content = readFileSync(configPath, "utf-8");
          const config = JSON.parse(content);
          const servers = config.mcpServers || config.servers || [];
          resolve({
            tag: "Right",
            value: servers.map(s => ({
              id: s.id || s.name,
              name: s.name,
              command: s.command,
              args: s.args || [],
              url: s.url,
              env: s.env ? Object.entries(s.env).map(([key, value]) => ({ key, value })) : null,
              timeout: s.timeout || 30000
            }))
          });
          return;
        }
      }

      // No config found, return empty array
      resolve({ tag: "Right", value: [] });
    } catch (e) {
      resolve({ tag: "Left", value: `Failed to load MCP config: ${e.message}` });
    }
  });
};

// Send JSON-RPC request and get response
function sendRPC(serverId, method, params) {
  return new Promise((resolve, reject) => {
    const conn = connections.get(serverId);
    if (!conn) {
      reject(new Error("Server not connected: " + serverId));
      return;
    }

    const id = ++requestId;
    const request = JSON.stringify({
      jsonrpc: "2.0",
      id,
      method,
      params: params || {}
    }) + "\n";

    // Register pending request
    conn.pending.set(id, { resolve, reject });

    // Set timeout
    const timeout = setTimeout(() => {
      conn.pending.delete(id);
      reject(new Error("Request timed out: " + method));
    }, conn.timeout || 30000);

    conn.pending.set(id, { resolve, reject, timeout });

    // Write to stdin
    try {
      conn.process.stdin.write(request);
    } catch (e) {
      conn.pending.delete(id);
      clearTimeout(timeout);
      reject(new Error("Failed to write to MCP server: " + e.message));
    }
  });
}

// Handle incoming JSON-RPC response data
function handleData(serverId, data) {
  const conn = connections.get(serverId);
  if (!conn) return;

  conn.buffer += data.toString();

  // Process complete JSON-RPC messages (newline-delimited)
  let newlineIdx;
  while ((newlineIdx = conn.buffer.indexOf("\n")) !== -1) {
    const line = conn.buffer.slice(0, newlineIdx).trim();
    conn.buffer = conn.buffer.slice(newlineIdx + 1);

    if (line.length === 0) continue;

    try {
      const msg = JSON.parse(line);

      if (msg.id != null && conn.pending.has(msg.id)) {
        const { resolve, reject, timeout } = conn.pending.get(msg.id);
        conn.pending.delete(msg.id);
        if (timeout) clearTimeout(timeout);

        if (msg.error) {
          reject(new Error(msg.error.message || JSON.stringify(msg.error)));
        } else {
          resolve(msg.result);
        }
      }
      // Ignore notifications (no id) for now
    } catch (e) {
      // Skip malformed JSON lines
    }
  }
}

// Connect to MCP server via stdio transport
export const connectServerFFI = (server) => () => {
  return new Promise((resolve) => {
    try {
      // Check transport type
      if (server.transport === "stdio" || server.transport.constructor.name === "StdioTransport") {
        // stdio transport - spawn process
        if (!server.name) {
          resolve({ tag: "Left", value: "No command configured for stdio server" });
          return;
        }

        // Build environment
        const env = { ...process.env };
        if (server.env) {
          for (const entry of server.env) {
            env[entry.key] = entry.value;
          }
        }

        // Spawn child process
        const proc = spawn(server.name, server.args || [], {
          stdio: ["pipe", "pipe", "pipe"],
          env
        });

        const conn = {
          process: proc,
          pending: new Map(),
          buffer: "",
          timeout: server.timeout || 30000
        };

        connections.set(server.id, conn);

        // Handle stdout data (JSON-RPC responses)
        proc.stdout.on("data", (data) => {
          handleData(server.id, data);
        });

        // Handle errors
        proc.on("error", (err) => {
          connections.delete(server.id);
        });

        proc.on("exit", (code) => {
          // Clean up pending requests
          const conn = connections.get(server.id);
          if (conn) {
            for (const [id, { reject, timeout }] of conn.pending) {
              if (timeout) clearTimeout(timeout);
              reject(new Error("MCP server exited with code: " + code));
            }
            conn.pending.clear();
          }
          connections.delete(server.id);
        });

        // Send initialize request
        sendRPC(server.id, "initialize", {
          protocolVersion: "2024-11-05",
          capabilities: {},
          clientInfo: { name: "forge", version: "1.0.0" }
        }).then((initResult) => {
          // Send initialized notification
          try {
            proc.stdin.write(JSON.stringify({
              jsonrpc: "2.0",
              method: "notifications/initialized"
            }) + "\n");
          } catch (e) { /* ignore */ }

          // Query tools
          return sendRPC(server.id, "tools/list", {});
        }).then((toolsResult) => {
          const tools = (toolsResult.tools || []).map(t => ({
            name: t.name,
            description: t.description || "",
            inputSchema: t.inputSchema || {}
          }));

          // Query resources
          return sendRPC(server.id, "resources/list", {}).then((resourcesResult) => {
            const resources = (resourcesResult.resources || []).map(r => ({
              uri: r.uri,
              name: r.name || r.uri,
              description: r.description || null,
              mimeType: r.mimeType || null
            }));

            resolve({
              tag: "Right",
              value: {
                ...server,
                tools,
                resources,
                connected: true
              }
            });
          }).catch(() => {
            // Resources list may not be supported
            resolve({
              tag: "Right",
              value: {
                ...server,
                tools,
                resources: [],
                connected: true
              }
            });
          });
        }).catch((err) => {
          // Clean up on init failure
          try { proc.kill(); } catch (e) { /* ignore */ }
          connections.delete(server.id);
          resolve({
            tag: "Left",
            value: "MCP initialization failed: " + err.message
          });
        });

      } else {
        // SSE transport
        resolve({
          tag: "Left",
          value: "SSE transport not yet supported (use stdio)"
        });
      }
    } catch (e) {
      resolve({
        tag: "Left",
        value: "Failed to connect to MCP server: " + e.message
      });
    }
  });
};

// Disconnect from MCP server
export const disconnectServerFFI = (server) => () => {
  return new Promise((resolve) => {
    try {
      const conn = connections.get(server.id);
      if (conn) {
        // Clean up pending requests
        for (const [id, { reject, timeout }] of conn.pending) {
          if (timeout) clearTimeout(timeout);
          reject(new Error("Server disconnected"));
        }
        conn.pending.clear();

        // Kill the process
        try { conn.process.kill(); } catch (e) { /* ignore */ }
        connections.delete(server.id);
      }
      resolve({ tag: "Right", value: undefined });
    } catch (e) {
      resolve({ tag: "Left", value: "Failed to disconnect: " + e.message });
    }
  });
};

// Call MCP tool via JSON-RPC
export const callToolFFI = (server) => (toolName) => (arguments_) => () => {
  return new Promise((resolve) => {
    sendRPC(server.id, "tools/call", {
      name: toolName,
      arguments: arguments_
    }).then((result) => {
      resolve({
        tag: "Right",
        value: {
          content: (result.content || []).map(c => ({
            blockType: c.type || "text",
            text: c.text || null,
            data: c.data || null,
            mimeType: c.mimeType || null
          })),
          isError: result.isError || false
        }
      });
    }).catch((err) => {
      resolve({
        tag: "Left",
        value: "MCP tool call failed: " + err.message
      });
    });
  });
};

// Read MCP resource via JSON-RPC
export const readResourceFFI = (server) => (uri) => () => {
  return new Promise((resolve) => {
    sendRPC(server.id, "resources/read", { uri }).then((result) => {
      // Extract text content from resource response
      const contents = result.contents || [];
      const textContent = contents
        .filter(c => c.text != null)
        .map(c => c.text)
        .join("\n");
      resolve({ tag: "Right", value: textContent });
    }).catch((err) => {
      resolve({
        tag: "Left",
        value: "MCP resource read failed: " + err.message
      });
    });
  });
};
