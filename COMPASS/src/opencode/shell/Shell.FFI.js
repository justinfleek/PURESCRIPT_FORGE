"use strict";

/**
 * Shell FFI
 * Provides shell detection utilities
 */

const os = require("os");
const path = require("path");
const { execSync } = require("child_process");

// | Get system default shell
exports.getSystemShell = function () {
  // Check environment variable first
  const envShell = process.env.SHELL;
  if (envShell) {
    return envShell;
  }
  
  // Platform-specific fallback
  if (process.platform === "win32") {
    // Try Git Bash if available
    try {
      const gitPath = execSync("where git", { encoding: "utf-8" }).trim();
      if (gitPath) {
        // git.exe is typically at: C:\Program Files\Git\cmd\git.exe
        // bash.exe is at: C:\Program Files\Git\bin\bash.exe
        const bashPath = path.join(path.dirname(gitPath), "..", "bin", "bash.exe");
        const fs = require("fs");
        if (fs.existsSync(bashPath)) {
          return bashPath;
        }
      }
    } catch (e) {
      // Fall through to default
    }
    
    // Default Windows shell
    return process.env.COMSPEC || "cmd.exe";
  }
  
  if (process.platform === "darwin") {
    return "/bin/zsh";
  }
  
  // Try bash, fallback to sh
  try {
    const bash = execSync("which bash", { encoding: "utf-8" }).trim();
    if (bash) {
      return bash;
    }
  } catch (e) {
    // Fall through
  }
  
  return "/bin/sh";
};
