// FFI for Forge.Server.Routes.Global
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/global.ts

import path from "path";
import os from "os";

// Lazy import to avoid circular dependencies
let Global = null;
async function getGlobal() {
  if (!Global) {
    Global = await import("../../global/Index.js").then(m => m.Global).catch(() => ({
      Path: {
        data: path.join(os.homedir(), ".opencode"),
        config: path.join(os.homedir(), ".config", "opencode"),
      },
    }));
  }
  return Global;
}

// Get global configuration and paths
export const getFFI = async () => {
  try {
    const global = await getGlobal();
    return {
      tag: "Right",
      value: {
        version: process.env.npm_package_version || "0.0.1",
        paths: {
          data: global?.Path?.data || path.join(os.homedir(), ".opencode"),
          config: global?.Path?.config || path.join(os.homedir(), ".config", "opencode"),
        },
        platform: process.platform,
        arch: process.arch,
        node: process.version,
      },
    };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get environment info
export const envFFI = async () => {
  try {
    return {
      tag: "Right",
      value: {
        NODE_ENV: process.env.NODE_ENV || "development",
        OPENCODE_DEBUG: process.env.OPENCODE_DEBUG || "",
        OPENCODE_CLIENT: process.env.OPENCODE_CLIENT || "cli",
      },
    };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
