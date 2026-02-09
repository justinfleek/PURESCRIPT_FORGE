// Forge.Project.Bootstrap FFI - Project initialization

import * as fs from 'fs/promises';
import * as path from 'path';

// Check if file/directory exists
export const existsFFI = (filePath) => async () => {
  try {
    await fs.access(filePath);
    return true;
  } catch {
    // Also check for glob patterns
    if (filePath.includes('*')) {
      try {
        const dir = path.dirname(filePath);
        const pattern = path.basename(filePath);
        const entries = await fs.readdir(dir);
        const regex = new RegExp('^' + pattern.replace('*', '.*') + '$');
        return entries.some(e => regex.test(e));
      } catch {
        return false;
      }
    }
    return false;
  }
};

// Create directory
export const mkdirFFI = (dirPath) => async () => {
  try {
    await fs.mkdir(dirPath, { recursive: true });
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Write file
export const writeFileFFI = (filePath) => (content) => async () => {
  try {
    await fs.writeFile(filePath, content, 'utf-8');
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// List directory
export const listDirFFI = (dirPath) => async () => {
  try {
    const entries = await fs.readdir(dirPath);
    return { tag: 'Right', value: entries };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Split path
export const splitImpl = (pathStr) => {
  return pathStr.split(/[/\\]/).filter(Boolean);
};
