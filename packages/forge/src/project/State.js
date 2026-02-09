// Forge.Project.State FFI - Project state management

import * as fs from 'fs/promises';
import * as path from 'path';

// Load state from file
export const loadStateFFI = (projectDir) => async () => {
  try {
    const statePath = path.join(projectDir, '.forge', 'state.json');
    const content = await fs.readFile(statePath, 'utf-8');
    const state = JSON.parse(content);
    return {
      isInitialized: state.isInitialized || false,
      hasConfig: state.hasConfig || false,
      lastUpdated: state.lastUpdated || Date.now(),
      lastSessionId: state.lastSessionId || null,
      settings: state.settings ? JSON.stringify(state.settings) : null
    };
  } catch {
    return null;
  }
};

// Save state to file
export const saveStateFFI = (projectDir) => (state) => async () => {
  try {
    const forgeDir = path.join(projectDir, '.forge');
    const statePath = path.join(forgeDir, 'state.json');
    
    // Ensure .forge directory exists
    await fs.mkdir(forgeDir, { recursive: true });
    
    const stateObj = {
      isInitialized: state.isInitialized,
      hasConfig: state.hasConfig,
      lastUpdated: state.lastUpdated,
      lastSessionId: state.lastSessionId,
      settings: state.settings ? JSON.parse(state.settings) : null
    };
    
    await fs.writeFile(statePath, JSON.stringify(stateObj, null, 2), 'utf-8');
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Delete state file
export const deleteStateFFI = (projectDir) => async () => {
  try {
    const statePath = path.join(projectDir, '.forge', 'state.json');
    await fs.unlink(statePath);
    return { tag: 'Right', value: {} };
  } catch (err) {
    if (err.code === 'ENOENT') {
      return { tag: 'Right', value: {} };
    }
    return { tag: 'Left', value: err.message };
  }
};

// Get current timestamp
export const nowFFI = async () => {
  return Date.now();
};
