// Forge.CLI.Cmd.Debug.Skill FFI

import * as fs from 'fs/promises';
import * as path from 'path';

export const debugSkillFFI = (name) => async () => {
  try {
    const skillDirs = [
      path.join(process.cwd(), '.forge', 'skills'),
      path.join(process.cwd(), 'skills')
    ];

    if (!name) {
      const allSkills = [];
      for (const dir of skillDirs) {
        try {
          const files = await fs.readdir(dir);
          for (const f of files) {
            allSkills.push(f);
          }
        } catch { /* dir may not exist */ }
      }
      console.log(JSON.stringify({ skills: allSkills }, null, 2));
      return { tag: 'Right', value: {} };
    }

    for (const dir of skillDirs) {
      try {
        const filePath = path.join(dir, name);
        const content = await fs.readFile(filePath, 'utf8');
        console.log(content);
        return { tag: 'Right', value: {} };
      } catch { /* try next */ }
    }

    return { tag: 'Left', value: 'Skill not found: ' + name };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
