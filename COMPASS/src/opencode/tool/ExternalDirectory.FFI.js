"use strict";

const path = require("path");
const fs = require("fs");

/**
 * Get project worktree root
 * In production, would use git worktree or project config
 */
exports.getWorktreeRoot = function () {
  // Try to find .git directory by walking up from current directory
  let currentDir = process.cwd();
  let maxDepth = 20; // Prevent infinite loops
  let depth = 0;
  
  while (depth < maxDepth) {
    const gitPath = path.join(currentDir, ".git");
    if (fs.existsSync(gitPath)) {
      return currentDir;
    }
    
    const parent = path.dirname(currentDir);
    if (parent === currentDir) {
      // Reached filesystem root
      break;
    }
    
    currentDir = parent;
    depth++;
  }
  
  // Fallback to current working directory
  return process.cwd();
};

/**
 * Normalize a file path
 */
exports.normalizePath = function (filePath) {
  // Resolve relative paths and normalize separators
  const resolved = path.resolve(filePath);
  return path.normalize(resolved);
};

/**
 * Check if path starts with prefix
 */
exports.pathStartsWith = function (filePath) {
  return function (prefix) {
    const normalizedPath = path.normalize(filePath);
    const normalizedPrefix = path.normalize(prefix);
    return normalizedPath.startsWith(normalizedPrefix);
  };
};
