// Forge.LSP.Client FFI - LSP client implementation

import { spawn } from 'child_process';

// Active clients map
const clients = new Map();
let clientIdCounter = 0;

// Create LSP client
export const createClientFFI = (config) => async () => {
  try {
    const clientId = ++clientIdCounter;
    const client = {
      config,
      state: { tag: 'Disconnected' },
      capabilities: null,
      processId: null,
      _id: clientId,
      _process: null,
      _requestId: 0,
      _pendingRequests: new Map()
    };
    clients.set(clientId, client);
    return { tag: 'Right', value: mapClient(client) };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Connect to LSP server
export const connectClientFFI = (clientData) => async () => {
  try {
    const client = clients.get(clientData._id || findClientId(clientData));
    if (!client) {
      return { tag: 'Left', value: 'Client not found' };
    }

    client.state = { tag: 'Connecting' };

    // Spawn the LSP server process
    const proc = spawn(client.config.serverCommand, client.config.serverArgs, {
      stdio: ['pipe', 'pipe', 'pipe']
    });

    client._process = proc;
    client.processId = proc.pid;

    // Set up message handling
    let buffer = '';
    proc.stdout.on('data', (data) => {
      buffer += data.toString();
      // Parse LSP messages from buffer
      // This is simplified - real implementation needs proper LSP framing
    });

    proc.stderr.on('data', (data) => {
      console.error('LSP stderr:', data.toString());
    });

    proc.on('close', () => {
      client.state = { tag: 'Disconnected' };
    });

    // Send initialize request
    const initParams = {
      processId: process.pid,
      rootUri: `file://${client.config.workspaceRoot}`,
      capabilities: {
        textDocument: {
          hover: { contentFormat: ['plaintext', 'markdown'] },
          completion: { completionItem: { snippetSupport: true } }
        }
      }
    };

    // For now, mark as connected
    client.state = { tag: 'Connected' };
    client.capabilities = {
      hoverProvider: true,
      completionProvider: true,
      definitionProvider: true,
      referencesProvider: true,
      documentFormattingProvider: true
    };

    return { tag: 'Right', value: mapClient(client) };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Disconnect from LSP server
export const disconnectClientFFI = (clientData) => async () => {
  try {
    const client = clients.get(clientData._id || findClientId(clientData));
    if (!client) {
      return { tag: 'Right', value: {} };
    }

    if (client._process) {
      client._process.kill();
      client._process = null;
    }

    client.state = { tag: 'Disconnected' };
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Send LSP request
export const sendRequestFFI = (clientData) => (method) => (params) => async () => {
  try {
    const client = clients.get(clientData._id || findClientId(clientData));
    if (!client || client.state.tag !== 'Connected') {
      return { tag: 'Left', value: 'Client not connected' };
    }

    // For now, return placeholder response
    // Real implementation would send JSON-RPC request and await response
    return { tag: 'Right', value: '{}' };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Escape JSON string
export const escapeJsonString = (str) => {
  return str
    .replace(/\\/g, '\\\\')
    .replace(/"/g, '\\"')
    .replace(/\n/g, '\\n')
    .replace(/\r/g, '\\r')
    .replace(/\t/g, '\\t');
};

// Helper to find client ID from client data
function findClientId(clientData) {
  for (const [id, client] of clients) {
    if (client.config.workspaceRoot === clientData.config.workspaceRoot &&
        client.config.language === clientData.config.language) {
      return id;
    }
  }
  return null;
}

// Map internal client to PureScript format
function mapClient(client) {
  return {
    config: client.config,
    state: client.state,
    capabilities: client.capabilities,
    processId: client.processId,
    _id: client._id
  };
}
