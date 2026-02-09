// Forge.CLI.Cmd.Debug.Agent FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { homedir } from 'os';

export const debugAgentFFI = async () => {
  try {
    const dirs = [
      path.join(homedir(), '.forge', 'agents'),
      path.join(process.cwd(), '.forge', 'agents')
    ];

    const result = { agents: [] };
    for (const dir of dirs) {
      try {
        const files = await fs.readdir(dir);
        for (const f of files) {
          const filePath = path.join(dir, f);
          const stat = await fs.stat(filePath);
          result.agents.push({
            name: f,
            path: filePath,
            size: stat.size,
            modified: stat.mtime.toISOString()
          });
        }
      } catch { /* dir may not exist */ }
    }

    console.log(JSON.stringify(result, null, 2));
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
