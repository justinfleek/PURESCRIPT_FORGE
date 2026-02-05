"use strict";

/**
 * Provider FFI
 * Provides config file location utilities
 */

const fs = require("fs");
const path = require("path");
const os = require("os");

// | Find opencode.json config file
exports.findConfigFile = function () {
  // Check current directory first
  const cwdConfig = path.join(process.cwd(), "opencode.json");
  if (fs.existsSync(cwdConfig)) {
    return cwdConfig;
  }
  
  // Check home directory
  const homeDir = os.homedir();
  const homeConfig = path.join(homeDir, ".opencode", "opencode.json");
  if (fs.existsSync(homeConfig)) {
    return homeConfig;
  }
  
  // Check XDG config directory
  const xdgConfigHome = process.env.XDG_CONFIG_HOME || path.join(homeDir, ".config");
  const xdgConfig = path.join(xdgConfigHome, "opencode", "opencode.json");
  if (fs.existsSync(xdgConfig)) {
    return xdgConfig;
  }
  
  // Not found
  return null;
};
