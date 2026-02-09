// Tool.Skill FFI - Directory listing and file reading for skill loading

import * as fs from 'fs/promises';
import * as path from 'path';

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

// Read file contents
export const readFileFFI = (filePath) => async () => {
  try {
    const content = await fs.readFile(filePath, 'utf-8');
    return { tag: 'Right', value: content };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
