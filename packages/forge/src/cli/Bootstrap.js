// Forge.CLI.Bootstrap FFI

import * as fs from 'fs/promises';
import * as path from 'path';
import { cwd } from 'process';

// Check if directory exists
export const directoryExistsFFI = (dirPath) => async () => {
  try {
    const stats = await fs.stat(dirPath);
    return stats.isDirectory();
  } catch {
    return false;
  }
};

// Create directory recursively
export const mkdirpFFI = (dirPath) => async () => {
  try {
    await fs.mkdir(dirPath, { recursive: true });
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get current working directory
export const cwdFFI = async () => {
  return cwd();
};
