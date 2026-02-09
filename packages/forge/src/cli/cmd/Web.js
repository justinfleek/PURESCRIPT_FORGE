// Forge.CLI.Cmd.Web FFI

import { exec } from 'child_process';
import { platform } from 'process';

export const openBrowserFFI = (url) => async () => {
  try {
    const cmd = platform === 'darwin' ? 'open'
              : platform === 'win32' ? 'start'
              : 'xdg-open';
    await new Promise((resolve, reject) => {
      exec(cmd + ' ' + JSON.stringify(url), (err) => {
        if (err) reject(err);
        else resolve();
      });
    });
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
