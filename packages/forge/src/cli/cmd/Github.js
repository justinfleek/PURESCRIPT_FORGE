// Forge.CLI.Cmd.Github FFI

import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

export const githubExecuteFFI = (action) => (repo) => async () => {
  try {
    try {
      await execAsync('gh --version');
    } catch {
      return { tag: 'Left', value: 'gh CLI not found. Install from https://cli.github.com/' };
    }

    let cmd;
    switch (action) {
      case 'status':
        cmd = repo ? 'gh repo view ' + repo : 'gh repo view';
        break;
      case 'clone':
        if (!repo) return { tag: 'Left', value: 'Repository required for clone' };
        cmd = 'gh repo clone ' + repo;
        break;
      case 'issues':
        cmd = repo ? 'gh issue list -R ' + repo : 'gh issue list';
        break;
      case 'prs':
        cmd = repo ? 'gh pr list -R ' + repo : 'gh pr list';
        break;
      default:
        cmd = 'gh repo view';
    }

    const { stdout } = await execAsync(cmd);
    if (stdout.trim()) console.log(stdout.trim());
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
