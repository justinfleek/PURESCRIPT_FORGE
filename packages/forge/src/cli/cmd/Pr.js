// Forge.CLI.Cmd.Pr FFI

import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

export const prExecuteFFI = (action) => (number) => (title) => (body) => async () => {
  try {
    // Check if gh is installed
    try {
      await execAsync('gh --version');
    } catch {
      return { tag: 'Left', value: 'gh CLI not found. Install from https://cli.github.com/' };
    }

    let cmd;
    switch (action) {
      case 'checkout':
        if (!number) return { tag: 'Left', value: 'PR number required for checkout' };
        cmd = 'gh pr checkout ' + number;
        break;
      case 'create':
        cmd = 'gh pr create';
        if (title) cmd += ' --title ' + JSON.stringify(title);
        if (body) cmd += ' --body ' + JSON.stringify(body);
        break;
      case 'view':
        cmd = number ? 'gh pr view ' + number : 'gh pr view';
        break;
      case 'merge':
        if (!number) return { tag: 'Left', value: 'PR number required for merge' };
        cmd = 'gh pr merge ' + number;
        break;
      case 'list':
        cmd = 'gh pr list';
        break;
      default:
        cmd = 'gh pr list';
    }

    const { stdout } = await execAsync(cmd);
    if (stdout.trim()) console.log(stdout.trim());
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
