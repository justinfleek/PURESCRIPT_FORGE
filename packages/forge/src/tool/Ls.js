// Tool.Ls FFI - Directory listing

import * as fs from 'fs/promises';

// List directory contents
export const listDirectoryFFI = (dirPath) => async () => {
  try {
    const entries = await fs.readdir(dirPath, { withFileTypes: true });
    const result = entries.map(entry => ({
      name: entry.name,
      isDirectory: entry.isDirectory()
    }));
    return { tag: 'Right', value: result };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
