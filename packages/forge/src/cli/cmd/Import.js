// Forge.CLI.Cmd.Import FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { homedir } from 'os';
import { randomUUID } from 'crypto';

export const importSessionFFI = (source) => async () => {
  try {
    let content;

    if (source.startsWith('http://') || source.startsWith('https://')) {
      const response = await fetch(source);
      if (!response.ok) {
        return { tag: 'Left', value: 'Failed to fetch: ' + response.statusText };
      }
      content = await response.text();
    } else {
      content = await fs.readFile(source, 'utf8');
    }

    const session = JSON.parse(content);
    const sessionId = session.id || randomUUID();
    const sessionsDir = path.join(homedir(), '.forge', 'data', 'sessions');
    await fs.mkdir(sessionsDir, { recursive: true });
    const targetPath = path.join(sessionsDir, sessionId + '.json');
    await fs.writeFile(targetPath, JSON.stringify(session, null, 2), 'utf8');
    console.log('Imported session: ' + sessionId);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
