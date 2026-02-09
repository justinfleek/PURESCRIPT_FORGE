// FFI for Forge.Project.Instance
// 1:1 parity with opencode-dev/packages/opencode/src/project/instance.ts

import { randomUUID } from "crypto";
import path from "path";
import fs from "fs/promises";

// State management helpers
const stateMap = new Map();

export function state(factory) {
  return async () => {
    const key = factory.toString();
    if (!stateMap.has(key)) {
      stateMap.set(key, await factory());
    }
    return stateMap.get(key);
  };
}

// Current instance state
let instance = {
  project: {
    id: "default",
    name: null,
    vcs: null,
  },
  directory: process.cwd(),
  worktree: process.cwd(),
};

// Get directory
export const directory = instance.directory;

// Get worktree
export const worktree = instance.worktree;

// Get project
export const project = instance.project;

// Check if path is contained in instance
export function containsPath(filepath) {
  const normalized = path.resolve(filepath);
  return normalized.startsWith(instance.directory) || normalized.startsWith(instance.worktree);
}

// Initialize instance
export async function initialize(dir) {
  instance.directory = dir || process.cwd();
  instance.worktree = dir || process.cwd();

  // Check for git repo
  try {
    await fs.access(path.join(instance.directory, ".git"));
    instance.project.vcs = "git";
    
    // Get git worktree root
    const { exec } = await import("child_process");
    const { promisify } = await import("util");
    const execAsync = promisify(exec);
    
    try {
      const { stdout } = await execAsync("git rev-parse --show-toplevel", {
        cwd: instance.directory,
      });
      instance.worktree = stdout.trim();
    } catch {
      // Not a git repo or command failed
    }
  } catch {
    // No .git directory
  }

  // Generate project ID from directory path
  const crypto = await import("crypto");
  instance.project.id = crypto.createHash("sha256").update(instance.directory).digest("hex").slice(0, 16);

  return instance;
}

// Instance namespace
export const Instance = {
  state,
  directory,
  worktree,
  project,
  containsPath,
  initialize,
  get: () => instance,
};

// Current instance
let currentInstance = instance;

// PureScript FFI exports
export const getCurrentInstanceFFI = async () => {
  return currentInstance;
};

export const setCurrentInstanceFFI = (inst) => async () => {
  currentInstance = inst;
  instance = inst;
};

export const clearCurrentInstanceFFI = async () => {
  currentInstance = null;
};

export const generateIdFFI = async () => {
  return randomUUID();
};

export const nowFFI = async () => {
  return Date.now();
};

export const containsPathFFI = (filepath) => containsPath(filepath);
