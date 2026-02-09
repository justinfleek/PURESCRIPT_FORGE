// Forge.CLI.Cmd.Acp FFI

import * as readline from 'readline';

export const acpExecuteFFI = (action) => (target) => async () => {
  try {
    if (action === 'serve') {
      const rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout,
        terminal: false
      });

      console.error('ACP server started, reading from stdin...');

      rl.on('line', (line) => {
        try {
          const request = JSON.parse(line);
          const response = {
            jsonrpc: '2.0',
            id: request.id,
            result: { status: 'ok', target: target }
          };
          process.stdout.write(JSON.stringify(response) + '\n');
        } catch (err) {
          const errorResponse = {
            jsonrpc: '2.0',
            id: null,
            error: { code: -32700, message: 'Parse error' }
          };
          process.stdout.write(JSON.stringify(errorResponse) + '\n');
        }
      });

      await new Promise((resolve) => {
        rl.on('close', resolve);
      });

      return { tag: 'Right', value: {} };
    }

    return { tag: 'Left', value: 'Unknown ACP action: ' + action };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
