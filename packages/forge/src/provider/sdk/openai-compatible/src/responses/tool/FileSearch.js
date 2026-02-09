// Forge.Provider.SDK.OpenAICompatible.Responses.Tool.FileSearch FFI

import { exec } from 'child_process';
import { promisify } from 'util';
import * as path from 'path';

const execAsync = promisify(exec);

export const searchFFI = (query) => (paths) => async () => {
  try {
    const results = [];
    const searchDirs = paths.length > 0 ? paths : [process.cwd()];

    for (const dir of searchDirs) {
      try {
        const { stdout } = await execAsync(
          'rg --json -l -m 10 ' + JSON.stringify(query) + ' ' + JSON.stringify(dir) + ' 2>/dev/null || true'
        );

        const lines = stdout.trim().split('\n').filter(Boolean);
        for (const line of lines) {
          try {
            const entry = JSON.parse(line);
            if (entry.type === 'match') {
              const filePath = entry.data.path.text;
              const content = entry.data.lines ? entry.data.lines.text || '' : '';
              results.push({
                fileId: filePath,
                filename: path.basename(filePath),
                score: 1.0,
                content: content.substring(0, 500)
              });
            }
          } catch { /* skip non-JSON lines */ }
        }
      } catch { /* skip errors for individual dirs */ }
    }

    return { tag: 'Right', value: results };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
