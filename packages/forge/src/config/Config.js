// FFI for Forge.Config.Config
// 1:1 parity with opencode-dev/packages/opencode/src/config/config.ts

import path from "path";
import fs from "fs/promises";
import os from "os";

// Default config
const DEFAULT_CONFIG = {
  share: "auto",
  theme: "system",
  experimental: {
    continue_loop_on_deny: false,
    openTelemetry: false,
  },
  username: null,
};

// Config state
let configCache = null;
let configPath = null;

// Get config directory
async function getConfigDir() {
  const platform = process.platform;
  if (platform === "darwin") {
    return path.join(os.homedir(), "Library", "Application Support", "opencode");
  } else if (platform === "win32") {
    return path.join(process.env.APPDATA || os.homedir(), "opencode");
  } else {
    return path.join(os.homedir(), ".config", "opencode");
  }
}

// Get config path
async function getConfigPath() {
  if (configPath) return configPath;
  const dir = await getConfigDir();
  configPath = path.join(dir, "config.json");
  return configPath;
}

// Load config from file
async function loadConfig() {
  const configFile = await getConfigPath();
  try {
    const content = await fs.readFile(configFile, "utf-8");
    return JSON.parse(content);
  } catch {
    return {};
  }
}

// Get config (with caching)
export async function get() {
  if (configCache) return configCache;
  const saved = await loadConfig();
  configCache = {
    ...DEFAULT_CONFIG,
    ...saved,
    experimental: {
      ...DEFAULT_CONFIG.experimental,
      ...saved.experimental,
    },
  };
  return configCache;
}

// Update config
export async function update(updater) {
  const current = await get();
  updater(current);
  configCache = current;
  
  const configFile = await getConfigPath();
  await fs.mkdir(path.dirname(configFile), { recursive: true });
  await fs.writeFile(configFile, JSON.stringify(current, null, 2));
  
  return current;
}

// Set specific config value
export async function set(key, value) {
  return update((config) => {
    const keys = key.split(".");
    let obj = config;
    for (let i = 0; i < keys.length - 1; i++) {
      if (!obj[keys[i]]) obj[keys[i]] = {};
      obj = obj[keys[i]];
    }
    obj[keys[keys.length - 1]] = value;
  });
}

// Clear config cache (for testing)
export function clearCache() {
  configCache = null;
}

// Config namespace
export const Config = {
  get,
  update,
  set,
  clearCache,
};

// PureScript FFI exports
export const getFFI = async () => {
  try {
    const config = await get();
    return { tag: "Right", value: config };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const updateFFI = (updater) => async () => {
  try {
    const config = await update(updater);
    return { tag: "Right", value: config };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
