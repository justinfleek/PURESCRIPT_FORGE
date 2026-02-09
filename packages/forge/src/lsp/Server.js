// Forge.LSP.Server FFI - LSP server management

import { spawn, exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

// Active servers
const servers = new Map();

// Start LSP server
export const startServerFFI = (language) => (config) => async () => {
  try {
    // Check if already running
    if (servers.has(language)) {
      const existing = servers.get(language);
      if (existing.status.tag === 'Running') {
        return { tag: 'Left', value: 'Server already running' };
      }
    }

    // Spawn the server process
    const proc = spawn(config.command, config.args, {
      stdio: ['pipe', 'pipe', 'pipe'],
      env: {
        ...process.env,
        ...Object.fromEntries(config.env.map(e => [e.key, e.value]))
      }
    });

    const server = {
      language,
      config,
      status: { tag: 'Running' },
      processId: proc.pid,
      capabilities: [],
      _process: proc
    };

    proc.on('close', (code) => {
      server.status = code === 0 
        ? { tag: 'Stopped' } 
        : { tag: 'Failed', value: `Exit code: ${code}` };
    });

    proc.on('error', (err) => {
      server.status = { tag: 'Failed', value: err.message };
    });

    servers.set(language, server);

    return {
      tag: 'Right',
      value: {
        language: server.language,
        config: server.config,
        status: server.status,
        processId: server.processId,
        capabilities: server.capabilities
      }
    };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Stop LSP server
export const stopServerFFI = (language) => async () => {
  try {
    const server = servers.get(language);
    if (!server) {
      return { tag: 'Right', value: {} };
    }

    if (server._process) {
      server.status = { tag: 'Stopping' };
      server._process.kill();
      server._process = null;
    }

    server.status = { tag: 'Stopped' };
    servers.delete(language);

    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get server status
export const getServerStatusFFI = (language) => async () => {
  const server = servers.get(language);
  if (!server) {
    return null;
  }
  return server.status;
};

// Check if command exists
export const checkCommandExistsFFI = (command) => async () => {
  try {
    // Try to find the command
    const checkCmd = process.platform === 'win32' 
      ? `where ${command}` 
      : `which ${command}`;
    await execAsync(checkCmd);
    return true;
  } catch {
    return false;
  }
};

// Traverse implementation
export const traverseImpl = (f) => (arr) => async () => {
  const results = [];
  for (const item of arr) {
    const result = await f(item)();
    results.push(result);
  }
  return results;
};
