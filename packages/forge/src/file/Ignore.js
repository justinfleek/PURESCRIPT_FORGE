// Forge.File.Ignore FFI - File ignore pattern utilities

import * as fs from 'fs/promises';
import * as path from 'path';

// Read file contents
export const readFileFFI = (filePath) => async () => {
  try {
    const content = await fs.readFile(filePath, 'utf-8');
    return { tag: 'Right', value: content };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Check if file exists
export const fileExistsFFI = (filePath) => async () => {
  try {
    await fs.access(filePath);
    return true;
  } catch {
    return false;
  }
};
