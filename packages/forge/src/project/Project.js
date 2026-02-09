// Forge.Project.Project FFI - Project information

import * as fs from 'fs/promises';
import * as path from 'path';
import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

// Check if file exists
export const fileExistsFFI = (filePath) => async () => {
  try {
    // Handle glob patterns
    if (filePath.includes('*')) {
      const dir = path.dirname(filePath);
      const pattern = path.basename(filePath);
      const entries = await fs.readdir(dir);
      const regex = new RegExp('^' + pattern.replace('*', '.*') + '$');
      return entries.some(e => regex.test(e));
    }
    await fs.access(filePath);
    return true;
  } catch {
    return false;
  }
};

// Find git root directory
export const findGitRootFFI = (directory) => async () => {
  try {
    const { stdout } = await execAsync('git rev-parse --show-toplevel', {
      cwd: directory
    });
    return stdout.trim();
  } catch {
    return null;
  }
};

// Get base name from path
export const getBaseNameFFI = (filePath) => {
  return path.basename(filePath);
};

// Traverse implementation
export const traverseImpl = (f) => (arr) => async () => {
  const results = [];
  for (const item of arr) {
    const result = await f(item)();
    results.push(result);
  }
  return results;
};
