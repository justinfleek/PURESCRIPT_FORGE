// Forge.CLI.Cmd.Mcp FFI

import * as fs from 'fs/promises';
import * as path from 'path';

export const mcpExecuteFFI = (list) => (addName) => (removeName) => (infoName) => async () => {
  try {
    const configPath = path.join(process.cwd(), 'opencode.json');
    let config;
    try {
      const content = await fs.readFile(configPath, 'utf8');
      config = JSON.parse(content);
    } catch {
      config = {};
    }

    const servers = config.mcpServers || {};

    if (infoName) {
      const server = servers[infoName];
      if (!server) {
        return { tag: 'Left', value: 'MCP server not found: ' + infoName };
      }
      console.log(JSON.stringify(server, null, 2));
      return { tag: 'Right', value: {} };
    }

    if (addName) {
      servers[addName] = { command: addName, args: [] };
      config.mcpServers = servers;
      await fs.writeFile(configPath, JSON.stringify(config, null, 2), 'utf8');
      console.log('Added MCP server: ' + addName);
      return { tag: 'Right', value: {} };
    }

    if (removeName) {
      if (!servers[removeName]) {
        return { tag: 'Left', value: 'MCP server not found: ' + removeName };
      }
      delete servers[removeName];
      config.mcpServers = servers;
      await fs.writeFile(configPath, JSON.stringify(config, null, 2), 'utf8');
      console.log('Removed MCP server: ' + removeName);
      return { tag: 'Right', value: {} };
    }

    // Default: list
    const names = Object.keys(servers);
    if (names.length === 0) {
      console.log('No MCP servers configured');
    } else {
      for (const name of names) {
        console.log('  ' + name + ': ' + (servers[name].command || 'unknown'));
      }
    }
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
