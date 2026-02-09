// Forge.CLI.Cmd.Export FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { homedir } from 'os';

export const exportSessionFFI = (sessionId) => (format) => (outputPath) => async () => {
  try {
    const sessionsDir = path.join(homedir(), '.forge', 'data', 'sessions');
    let targetId = sessionId;

    if (!targetId) {
      try {
        const files = await fs.readdir(sessionsDir);
        const jsonFiles = files.filter(f => f.endsWith('.json'));
        if (jsonFiles.length === 0) {
          return { tag: 'Left', value: 'No sessions found' };
        }
        const stats = await Promise.all(jsonFiles.map(async f => ({
          name: f,
          mtime: (await fs.stat(path.join(sessionsDir, f))).mtimeMs
        })));
        stats.sort((a, b) => b.mtime - a.mtime);
        targetId = stats[0].name.replace('.json', '');
      } catch {
        return { tag: 'Left', value: 'No sessions directory found' };
      }
    }

    const sessionPath = path.join(sessionsDir, targetId + '.json');
    const content = await fs.readFile(sessionPath, 'utf8');
    const session = JSON.parse(content);

    let output;
    if (format === 'markdown') {
      const lines = ['# Session: ' + targetId, ''];
      if (session.messages) {
        for (const msg of session.messages) {
          lines.push('## ' + (msg.role || 'unknown'));
          lines.push('');
          lines.push(msg.content || '');
          lines.push('');
        }
      }
      output = lines.join('\n');
    } else {
      output = JSON.stringify(session, null, 2);
    }

    if (outputPath) {
      await fs.writeFile(outputPath, output, 'utf8');
      console.log('Exported session ' + targetId + ' to ' + outputPath);
    } else {
      console.log(output);
    }

    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
