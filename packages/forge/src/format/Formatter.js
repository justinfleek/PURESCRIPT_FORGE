// Forge.Format.Formatter FFI - Code formatting

import { spawn } from 'child_process';
import * as fs from 'fs/promises';

// Run a formatter on code
export const runFormatterFFI = (formatter) => (code) => (args) => async () => {
  return new Promise((resolve) => {
    const proc = spawn(formatter, [...args, '--stdin-filepath', 'stdin'], {
      stdio: ['pipe', 'pipe', 'pipe']
    });
    
    let stdout = '';
    let stderr = '';
    
    proc.stdout.on('data', (data) => {
      stdout += data.toString();
    });
    
    proc.stderr.on('data', (data) => {
      stderr += data.toString();
    });
    
    proc.on('close', (exitCode) => {
      if (exitCode !== 0) {
        resolve({ tag: 'Left', value: stderr || `Formatter exited with code ${exitCode}` });
      } else {
        resolve({ tag: 'Right', value: stdout });
      }
    });
    
    proc.on('error', (err) => {
      resolve({ tag: 'Left', value: err.message });
    });
    
    // Write code to stdin
    proc.stdin.write(code);
    proc.stdin.end();
    
    // Timeout after 10 seconds
    setTimeout(() => {
      proc.kill();
      resolve({ tag: 'Left', value: 'Formatter timeout' });
    }, 10000);
  });
};

// Check if formatter is available
export const checkFormatterFFI = (formatter) => async () => {
  return new Promise((resolve) => {
    const proc = spawn(formatter, ['--version'], {
      stdio: ['pipe', 'pipe', 'pipe']
    });
    
    proc.on('close', (exitCode) => {
      resolve(exitCode === 0);
    });
    
    proc.on('error', () => {
      resolve(false);
    });
    
    // Timeout
    setTimeout(() => {
      proc.kill();
      resolve(false);
    }, 2000);
  });
};

// Read file
export const readFileFFI = (path) => async () => {
  try {
    const content = await fs.readFile(path, 'utf-8');
    return { tag: 'Right', value: content };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Write file
export const writeFileFFI = (path) => (content) => async () => {
  try {
    await fs.writeFile(path, content, 'utf-8');
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Traverse array with async function
export const traverseAff = (f) => (arr) => async () => {
  const results = [];
  for (const item of arr) {
    const result = await f(item)();
    results.push(result);
  }
  return results;
};
