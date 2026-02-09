// Forge.File.Time FFI - File timestamp operations

import * as fs from 'fs/promises';

// Get file stats (timestamps)
export const getFileStatsFFI = (filePath) => async () => {
  try {
    const stats = await fs.stat(filePath);
    return {
      tag: 'Right',
      value: {
        created: stats.birthtime.getTime(),
        modified: stats.mtime.getTime(),
        accessed: stats.atime.getTime()
      }
    };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Touch a file (update modification time)
export const touchFileFFI = (filePath) => async () => {
  try {
    const now = new Date();
    await fs.utimes(filePath, now, now);
    return { tag: 'Right', value: {} };
  } catch (err) {
    // If file doesn't exist, try to create it
    if (err.code === 'ENOENT') {
      try {
        await fs.writeFile(filePath, '', { flag: 'a' });
        return { tag: 'Right', value: {} };
      } catch (createErr) {
        return { tag: 'Left', value: createErr.message };
      }
    }
    return { tag: 'Left', value: err.message };
  }
};
