// FFI for Forge.Server.Routes.Config
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/config.ts

import { Config } from "../../config/Config.js";

// Get current config
export const getFFI = async () => {
  try {
    const config = await Config.get();
    return { tag: "Right", value: config };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Update config
export const updateFFI = (updates) => async () => {
  try {
    await Config.update((config) => {
      Object.assign(config, updates);
    });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Set specific config key
export const setFFI = (key) => (value) => async () => {
  try {
    await Config.set(key, value);
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
