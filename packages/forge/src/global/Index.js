// FFI for Forge.Global.Index
// 1:1 parity with opencode-dev/packages/opencode/src/global/global.ts

import path from "path";
import os from "os";
import fs from "fs/promises";

// Get platform-specific paths
function getDataDir() {
  const platform = process.platform;
  if (platform === "darwin") {
    return path.join(os.homedir(), "Library", "Application Support", "opencode");
  } else if (platform === "win32") {
    return path.join(process.env.APPDATA || os.homedir(), "opencode");
  } else {
    return path.join(os.homedir(), ".local", "share", "opencode");
  }
}

function getConfigDir() {
  const platform = process.platform;
  if (platform === "darwin") {
    return path.join(os.homedir(), "Library", "Application Support", "opencode");
  } else if (platform === "win32") {
    return path.join(process.env.APPDATA || os.homedir(), "opencode");
  } else {
    return path.join(os.homedir(), ".config", "opencode");
  }
}

// Path configuration (internal - not exported directly to avoid PS FFI issues)
const Path = {
  data: getDataDir(),
  config: getConfigDir(),
  worktree: process.cwd(),
  directory: process.cwd(),
  state: path.join(getDataDir(), "state"),
  cache: path.join(getDataDir(), "cache"),
  logs: path.join(getDataDir(), "logs"),
};

// Ensure directories exist
async function ensureDirectories() {
  const dirs = [Path.data, Path.config, Path.state, Path.cache, Path.logs];
  for (const dir of dirs) {
    await fs.mkdir(dir, { recursive: true }).catch(() => {});
  }
}

// Initialize on module load
ensureDirectories().catch(console.error);

// Global namespace (internal - not exported directly to avoid PS FFI issues)
const Global = {
  Path,
  ensureDirectories,
};

// PureScript FFI exports (lowercase for valid PS identifiers)
export const pathFFI = Path;
export const ensureDirectoriesFFI = () => ensureDirectories();

// Remove invalid uppercase exports (they break PS FFI compilation)
// The Path and Global objects are available via pathFFI for PureScript
// and can be imported directly by JS consumers
