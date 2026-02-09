// Forge.CLI.Cmd.Debug.Ripgrep FFI

import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

export const debugRipgrepFFI = (pattern) => async () => {
  try {
    try {
      const { stdout: version } = await execAsync('rg --version');
      console.log('Ripgrep version: ' + version.trim().split('\n')[0]);
    } catch {
      return { tag: 'Left', value: 'ripgrep (rg) not found in PATH' };
    }

    const { stdout } = await execAsync('rg --count-matches ' + JSON.stringify(pattern) + ' . 2>/dev/null || true');
    const lines = stdout.trim().split('\n').filter(Boolean);
    console.log('Pattern: ' + pattern);
    console.log('Matches in ' + lines.length + ' files');
    for (const line of lines.slice(0, 20)) {
      console.log('  ' + line);
    }
    if (lines.length > 20) {
      console.log('  ... and ' + (lines.length - 20) + ' more files');
    }
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
