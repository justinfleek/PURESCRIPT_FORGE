// Forge.Project.VCS FFI - Version control system integration

import { exec } from 'child_process';
import { promisify } from 'util';
import * as fs from 'fs/promises';
import * as path from 'path';

const execAsync = promisify(exec);

// Detect VCS in directory
export const detectVCSFFI = (directory) => async () => {
  try {
    // Check for .git
    try {
      const { stdout } = await execAsync('git rev-parse --show-toplevel', { cwd: directory });
      return { vcsType: 'git', root: stdout.trim() };
    } catch {}
    
    // Check for .hg
    try {
      await fs.access(path.join(directory, '.hg'));
      return { vcsType: 'hg', root: directory };
    } catch {}
    
    // Check for .svn
    try {
      await fs.access(path.join(directory, '.svn'));
      return { vcsType: 'svn', root: directory };
    } catch {}
    
    return null;
  } catch {
    return null;
  }
};

// Get current git branch
export const gitBranchFFI = (directory) => async () => {
  try {
    const { stdout } = await execAsync('git branch --show-current', { cwd: directory });
    const branch = stdout.trim();
    return branch || null;
  } catch {
    return null;
  }
};

// Get git status
export const gitStatusFFI = (directory) => async () => {
  try {
    const { stdout } = await execAsync('git status --porcelain -b', { cwd: directory });
    const lines = stdout.split('\n').filter(Boolean);
    
    const staged = [];
    const unstaged = [];
    const untracked = [];
    const conflicts = [];
    let ahead = 0;
    let behind = 0;
    
    for (const line of lines) {
      if (line.startsWith('##')) {
        // Branch info
        const match = line.match(/ahead (\d+)/);
        if (match) ahead = parseInt(match[1], 10);
        const behindMatch = line.match(/behind (\d+)/);
        if (behindMatch) behind = parseInt(behindMatch[1], 10);
        continue;
      }
      
      const indexStatus = line[0];
      const workTreeStatus = line[1];
      const file = line.slice(3);
      
      if (indexStatus === '?' && workTreeStatus === '?') {
        untracked.push(file);
      } else if (indexStatus === 'U' || workTreeStatus === 'U') {
        conflicts.push(file);
      } else {
        if (indexStatus !== ' ' && indexStatus !== '?') {
          staged.push(file);
        }
        if (workTreeStatus !== ' ' && workTreeStatus !== '?') {
          unstaged.push(file);
        }
      }
    }
    
    return {
      tag: 'Right',
      value: { staged, unstaged, untracked, conflicts, ahead, behind }
    };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get git diff
export const gitDiffFFI = (directory) => (filePath) => async () => {
  try {
    const cmd = filePath 
      ? `git diff -- "${filePath}"`
      : 'git diff';
    const { stdout } = await execAsync(cmd, { cwd: directory });
    return { tag: 'Right', value: stdout };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get git remote URL
export const gitRemoteFFI = (directory) => async () => {
  try {
    const { stdout } = await execAsync('git remote get-url origin', { cwd: directory });
    return stdout.trim() || null;
  } catch {
    return null;
  }
};
