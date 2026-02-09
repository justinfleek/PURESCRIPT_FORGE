// Forge.CLI.Cmd.Debug.Lsp FFI

import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

export const debugLspFFI = async () => {
  try {
    const servers = [];

    const checks = [
      { name: 'typescript-language-server', cmd: 'typescript-language-server --version' },
      { name: 'purescript-language-server', cmd: 'purescript-language-server --version' },
      { name: 'haskell-language-server', cmd: 'haskell-language-server-wrapper --version' },
      { name: 'rust-analyzer', cmd: 'rust-analyzer --version' }
    ];

    for (const check of checks) {
      try {
        const { stdout } = await execAsync(check.cmd + ' 2>&1');
        servers.push({ name: check.name, status: 'available', version: stdout.trim().split('\n')[0] });
      } catch {
        servers.push({ name: check.name, status: 'not found' });
      }
    }

    console.log(JSON.stringify({ languageServers: servers }, null, 2));
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
