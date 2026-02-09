// Forge.CLI.Cmd.Debug.Config FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { homedir } from 'os';

export const readConfigFFI = async () => {
  try {
    const configPath = path.join(homedir(), '.forge', 'config.json');
    const content = await fs.readFile(configPath, 'utf8');
    console.log(JSON.stringify(JSON.parse(content), null, 2));
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
