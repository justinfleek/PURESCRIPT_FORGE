// Forge.CLI.Cmd.Stats FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { homedir } from 'os';

export const statsFFI = (period) => (format) => async () => {
  try {
    const sessionsDir = path.join(homedir(), '.forge', 'data', 'sessions');
    let files;
    try {
      files = await fs.readdir(sessionsDir);
    } catch {
      files = [];
    }
    const jsonFiles = files.filter(f => f.endsWith('.json'));

    const now = Date.now();
    const periodMs = period === 'day' ? 86400000
                   : period === 'week' ? 604800000
                   : period === 'month' ? 2592000000
                   : Infinity;

    let totalSessions = 0;
    let totalMessages = 0;
    let totalInputTokens = 0;
    let totalOutputTokens = 0;

    for (const file of jsonFiles) {
      const filePath = path.join(sessionsDir, file);
      const stat = await fs.stat(filePath);

      if (now - stat.mtimeMs > periodMs) continue;

      totalSessions++;
      try {
        const content = await fs.readFile(filePath, 'utf8');
        const session = JSON.parse(content);
        if (session.messages) totalMessages += session.messages.length;
        if (session.usage) {
          totalInputTokens += session.usage.inputTokens || 0;
          totalOutputTokens += session.usage.outputTokens || 0;
        }
      } catch { /* skip malformed sessions */ }
    }

    const stats = {
      period: period || 'all',
      sessions: totalSessions,
      messages: totalMessages,
      inputTokens: totalInputTokens,
      outputTokens: totalOutputTokens,
      totalTokens: totalInputTokens + totalOutputTokens
    };

    if (format === 'json') {
      console.log(JSON.stringify(stats, null, 2));
    } else {
      console.log('Period:        ' + stats.period);
      console.log('Sessions:      ' + stats.sessions);
      console.log('Messages:      ' + stats.messages);
      console.log('Input tokens:  ' + stats.inputTokens);
      console.log('Output tokens: ' + stats.outputTokens);
      console.log('Total tokens:  ' + stats.totalTokens);
    }

    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
