// Forge.File.Ripgrep FFI - Ripgrep integration

import { spawn } from 'child_process';
import { promisify } from 'util';
import { exec } from 'child_process';

const execAsync = promisify(exec);

// Execute ripgrep with given arguments
export const executeRipgrepFFI = (args) => (searchPath) => async () => {
  return new Promise((resolve) => {
    const rg = spawn('rg', [...args, searchPath], {
      stdio: ['pipe', 'pipe', 'pipe'],
      maxBuffer: 10 * 1024 * 1024 // 10MB buffer
    });

    let stdout = '';
    let stderr = '';

    rg.stdout.on('data', (data) => {
      stdout += data.toString();
    });

    rg.stderr.on('data', (data) => {
      stderr += data.toString();
    });

    rg.on('close', (exitCode) => {
      // Exit code 1 = no matches (not an error)
      if (exitCode >= 2 && stderr) {
        resolve({ tag: 'Left', value: stderr });
      } else {
        resolve({ tag: 'Right', value: { stdout, exitCode: exitCode || 0 } });
      }
    });

    rg.on('error', (err) => {
      resolve({ tag: 'Left', value: err.message });
    });

    // Set timeout (30 seconds)
    setTimeout(() => {
      rg.kill();
      resolve({ tag: 'Left', value: 'Ripgrep timeout (30s)' });
    }, 30000);
  });
};

// Check if ripgrep is available
export const checkRipgrepFFI = async () => {
  try {
    await execAsync('rg --version');
    return true;
  } catch {
    return false;
  }
};

// Parse integer
export const parseIntFFI = (s) => {
  const n = parseInt(s, 10);
  return isNaN(n) ? -1 : n;
};
