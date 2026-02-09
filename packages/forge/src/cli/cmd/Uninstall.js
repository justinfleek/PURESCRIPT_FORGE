// Forge.CLI.Cmd.Uninstall FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { homedir } from 'os';

export const uninstallFFI = (force) => (keepData) => async () => {
  try {
    const home = homedir();
    const forgeDir = path.join(home, '.forge');
    const removed = [];

    try {
      await fs.access(forgeDir);
    } catch {
      return { tag: 'Left', value: 'Forge directory not found: ' + forgeDir };
    }

    if (!keepData) {
      const dataDir = path.join(forgeDir, 'data');
      try {
        await fs.rm(dataDir, { recursive: true, force: true });
        removed.push(dataDir);
      } catch { /* data dir may not exist */ }
    }

    if (force) {
      const configFile = path.join(forgeDir, 'config.json');
      try {
        await fs.rm(configFile, { force: true });
        removed.push(configFile);
      } catch { /* config may not exist */ }
    }

    console.log('Removed: ' + removed.join(', '));
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
