// Forge.LSP.Index FFI - LSP main entry point

import * as fs from 'fs/promises';

// Global LSP state
let lspState = null;

// Get LSP state
export const getStateFFI = async () => {
  return lspState;
};

// Set LSP state
export const setStateFFI = (state) => async () => {
  lspState = state;
};

// Get server command for a language
export const getServerCommandFFI = (language) => async () => {
  const servers = {
    'typescript': { command: 'typescript-language-server', args: ['--stdio'] },
    'typescriptreact': { command: 'typescript-language-server', args: ['--stdio'] },
    'javascript': { command: 'typescript-language-server', args: ['--stdio'] },
    'javascriptreact': { command: 'typescript-language-server', args: ['--stdio'] },
    'rust': { command: 'rust-analyzer', args: [] },
    'go': { command: 'gopls', args: ['serve'] },
    'python': { command: 'pyright-langserver', args: ['--stdio'] },
    'haskell': { command: 'haskell-language-server-wrapper', args: ['--lsp'] },
    'purescript': { command: 'purescript-language-server', args: ['--stdio'] },
    'json': { command: 'vscode-json-language-server', args: ['--stdio'] },
    'html': { command: 'vscode-html-language-server', args: ['--stdio'] },
    'css': { command: 'vscode-css-language-server', args: ['--stdio'] }
  };
  
  return servers[language] || null;
};

// Read file content
export const readFileFFI = (path) => async () => {
  try {
    const content = await fs.readFile(path, 'utf-8');
    return { tag: 'Right', value: content };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Traverse array with async function
export const traverse = (f) => (arr) => async () => {
  const results = [];
  for (const item of arr) {
    const result = await f(item)();
    results.push(result);
  }
  return results;
};
