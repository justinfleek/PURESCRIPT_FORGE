// Forge.CLI.Upgrade FFI

import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

// Fetch latest version from npm registry
export const fetchLatestVersionFFI = (packageName) => async () => {
  try {
    // In production, this would query npm registry
    // For now, return a placeholder
    const response = await fetch(`https://registry.npmjs.org/${packageName}/latest`);
    
    if (!response.ok) {
      // Return a default version if can't fetch
      return {
        tag: 'Right',
        value: {
          version: '0.1.0',
          notes: null,
          url: null
        }
      };
    }
    
    const data = await response.json();
    return {
      tag: 'Right',
      value: {
        version: data.version || '0.1.0',
        notes: data.description || null,
        url: data.homepage || null
      }
    };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Execute upgrade command
export const executeUpgradeFFI = (version) => async () => {
  try {
    // Determine package manager
    const pm = process.env.npm_execpath?.includes('yarn') ? 'yarn' : 
               process.env.npm_execpath?.includes('pnpm') ? 'pnpm' : 'npm';
    
    const cmd = pm === 'npm' 
      ? `npm install -g forge@${version}`
      : pm === 'yarn'
        ? `yarn global add forge@${version}`
        : `pnpm add -g forge@${version}`;
    
    await execAsync(cmd);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Parse integer
export const parseIntFFI = (s) => {
  const n = parseInt(s, 10);
  return isNaN(n) ? -1 : n;
};
