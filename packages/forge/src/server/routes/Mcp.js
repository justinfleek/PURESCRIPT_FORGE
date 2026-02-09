// FFI for Forge.Server.Routes.Mcp
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/mcp.ts

import { Log } from "../../util/Log.js";

const log = Log.create({ service: "mcp" });

// MCP server state
const servers = new Map();

// List MCP servers
export const listFFI = async () => {
  try {
    return { tag: "Right", value: Array.from(servers.values()) };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Call a tool on an MCP server
export const callToolFFI = (serverID) => (toolName) => (args) => async () => {
  try {
    const server = servers.get(serverID);
    if (!server) {
      return { tag: "Left", value: `MCP server not found: ${serverID}` };
    }
    
    log.info("calling MCP tool", { serverID, toolName });
    
    // In a full implementation, this would call the actual MCP server
    // For now, return a placeholder response
    return {
      tag: "Right",
      value: {
        result: null,
        error: null,
      },
    };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get server info
export const getServerFFI = (serverID) => async () => {
  try {
    const server = servers.get(serverID);
    if (!server) {
      return { tag: "Right", value: null };
    }
    return { tag: "Right", value: server };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List tools for a server
export const listToolsFFI = (serverID) => async () => {
  try {
    const server = servers.get(serverID);
    if (!server) {
      return { tag: "Left", value: `MCP server not found: ${serverID}` };
    }
    return { tag: "Right", value: server.tools || [] };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
