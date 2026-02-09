// Forge.CLI.Cmd.Agent FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { homedir } from 'os';

export const listAgentsFFI = async () => {
  try {
    const dirs = [
      path.join(homedir(), '.forge', 'agents'),
      path.join(process.cwd(), '.forge', 'agents')
    ];
    const agents = new Set();
    for (const dir of dirs) {
      try {
        const files = await fs.readdir(dir);
        for (const f of files) {
          if (f.endsWith('.json') || f.endsWith('.yaml') || f.endsWith('.yml')) {
            agents.add(f.replace(/\.(json|ya?ml)$/, ''));
          }
        }
      } catch { /* dir may not exist */ }
    }
    return { tag: 'Right', value: Array.from(agents) };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

export const showAgentInfoFFI = (name) => async () => {
  try {
    const dirs = [
      path.join(homedir(), '.forge', 'agents'),
      path.join(process.cwd(), '.forge', 'agents')
    ];
    for (const dir of dirs) {
      for (const ext of ['.json', '.yaml', '.yml']) {
        try {
          const filePath = path.join(dir, name + ext);
          const content = await fs.readFile(filePath, 'utf8');
          console.log(content);
          return { tag: 'Right', value: {} };
        } catch { /* try next */ }
      }
    }
    return { tag: 'Left', value: 'Agent not found: ' + name };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

export const printLinesFFI = (lines) => async () => {
  for (const line of lines) {
    console.log(line);
  }
};
