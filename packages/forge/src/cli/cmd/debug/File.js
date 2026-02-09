// Forge.CLI.Cmd.Debug.File FFI

import * as fs from 'fs/promises';

export const debugFileFFI = (filePath) => async () => {
  try {
    const stat = await fs.stat(filePath);
    const info = {
      path: filePath,
      size: stat.size,
      isFile: stat.isFile(),
      isDirectory: stat.isDirectory(),
      modified: stat.mtime.toISOString(),
      created: stat.birthtime.toISOString()
    };
    console.log(JSON.stringify(info, null, 2));
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
