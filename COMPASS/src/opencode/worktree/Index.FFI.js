"use strict";

/**
 * Worktree FFI
 * Provides Git worktree management utilities
 */

const { execSync } = require("child_process");
const path = require("path");

// | List worktrees
exports.listWorktrees = function () {
  return new Promise(function (resolve) {
    try {
      const output = execSync("git worktree list --porcelain", { encoding: "utf-8" });
      const worktrees = parseWorktreeList(output);
      resolve({
        tag: "Right",
        value: worktrees
      });
    } catch (error) {
      resolve({
        tag: "Left",
        value: error.message || "Failed to list worktrees"
      });
    }
  });
};

// | Create a worktree
exports.createWorktree = function (worktreePath) {
  return function (branch) {
    return function () {
      return new Promise(function (resolve) {
        try {
          execSync(`git worktree add ${worktreePath} ${branch}`, { encoding: "utf-8" });
          const worktree = {
            path: worktreePath,
            branch: branch,
            isMain: false
          };
          resolve({
            tag: "Right",
            value: worktree
          });
        } catch (error) {
          resolve({
            tag: "Left",
            value: error.message || "Failed to create worktree"
          });
        }
      });
    };
  };
};

// | Remove a worktree
exports.removeWorktree = function (worktreePath) {
  return function () {
    return new Promise(function (resolve) {
      try {
        execSync(`git worktree remove ${worktreePath}`, { encoding: "utf-8" });
        resolve({
          tag: "Right",
          value: null
        });
      } catch (error) {
        resolve({
          tag: "Left",
          value: error.message || "Failed to remove worktree"
        });
      }
    });
  };
};

// | Parse worktree list output
function parseWorktreeList(output) {
  const lines = output.split("\n");
  const worktrees = [];
  let current = null;
  
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (line.startsWith("worktree ")) {
      if (current) worktrees.push(current);
      current = {
        path: line.substring(9).trim(),
        branch: "",
        isMain: false
      };
    } else if (line.startsWith("HEAD ") && current) {
      const head = line.substring(5).trim();
      // Extract branch from HEAD (e.g., "refs/heads/main" -> "main")
      const branchMatch = head.match(/refs\/heads\/(.+)/);
      current.branch = branchMatch ? branchMatch[1] : head;
    } else if (line.startsWith("bare") && current) {
      current.isMain = true;
    }
  }
  
  if (current) worktrees.push(current);
  
  return worktrees;
}
