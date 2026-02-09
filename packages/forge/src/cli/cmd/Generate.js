// Forge.CLI.Cmd.Generate FFI

import * as fs from 'fs/promises';
import * as path from 'path';

const templates = {
  'default': {
    files: {
      'opencode.json': JSON.stringify({ version: '1.0', provider: 'anthropic', model: 'claude-sonnet-4-20250514' }, null, 2),
      '.forge/config.json': JSON.stringify({ features: { streaming: true, tools: true } }, null, 2)
    }
  },
  'minimal': {
    files: {
      'opencode.json': JSON.stringify({ version: '1.0', provider: 'anthropic' }, null, 2)
    }
  }
};

export const generateFFI = (template) => (outputDir) => (force) => async () => {
  try {
    const tmpl = templates[template];
    if (!tmpl) {
      return { tag: 'Left', value: 'Unknown template: ' + template + '. Available: ' + Object.keys(templates).join(', ') };
    }

    await fs.mkdir(outputDir, { recursive: true });

    for (const [filePath, content] of Object.entries(tmpl.files)) {
      const fullPath = path.join(outputDir, filePath);
      await fs.mkdir(path.dirname(fullPath), { recursive: true });

      if (!force) {
        try {
          await fs.access(fullPath);
          return { tag: 'Left', value: 'File already exists: ' + fullPath + '. Use --force to overwrite.' };
        } catch { /* file doesn't exist, continue */ }
      }

      await fs.writeFile(fullPath, content, 'utf8');
    }

    console.log('Generated ' + template + ' template in ' + outputDir);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
