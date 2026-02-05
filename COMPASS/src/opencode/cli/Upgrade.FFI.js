"use strict";

/**
 * CLI Upgrade FFI
 * Provides version reading utilities
 */

const fs = require("fs");
const path = require("path");

// | Read version from package.json
exports.readPackageVersion = function () {
  try {
    // Try to find package.json in current directory or parent directories
    let currentDir = process.cwd();
    let maxDepth = 5;
    let depth = 0;
    
    while (depth < maxDepth) {
      const packagePath = path.join(currentDir, "package.json");
      if (fs.existsSync(packagePath)) {
        const packageJson = JSON.parse(fs.readFileSync(packagePath, "utf-8"));
        if (packageJson.version) {
          return packageJson.version;
        }
      }
      
      const parent = path.dirname(currentDir);
      if (parent === currentDir) {
        break;
      }
      currentDir = parent;
      depth++;
    }
    
    return null;
  } catch (error) {
    return null;
  }
};
