// FFI for Forge.Server.Routes.Project
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/project.ts

import path from "path";
import fs from "fs/promises";

// Lazy import Instance to avoid circular dependencies
let Instance = null;
async function getInstance() {
  if (!Instance) {
    const mod = await import("../../project/Instance.js").catch(() => ({}));
    Instance = mod.Instance || { project: { id: "default" }, directory: process.cwd(), worktree: process.cwd() };
  }
  return Instance;
}

// Get project info
export const getFFI = async () => {
  try {
    const inst = await getInstance();
    return {
      tag: "Right",
      value: {
        id: inst?.project?.id || "default",
        directory: inst?.directory || process.cwd(),
        worktree: inst?.worktree || process.cwd(),
        vcs: inst?.project?.vcs || null,
      },
    };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List files in project
export const listFilesFFI = async () => {
  try {
    const inst = await getInstance();
    const dir = inst?.directory || process.cwd();
    
    const files = [];
    const entries = await fs.readdir(dir, { withFileTypes: true });
    
    for (const entry of entries) {
      if (entry.name.startsWith(".")) continue;
      files.push({
        name: entry.name,
        path: path.join(dir, entry.name),
        isDirectory: entry.isDirectory(),
      });
    }
    
    return { tag: "Right", value: files };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get file tree
export const treeFFI = (maxDepth) => async () => {
  try {
    const inst = await getInstance();
    const dir = inst?.directory || process.cwd();
    
    async function walk(currentDir, depth) {
      if (depth > maxDepth) return [];
      
      const entries = await fs.readdir(currentDir, { withFileTypes: true });
      const result = [];
      
      for (const entry of entries) {
        if (entry.name.startsWith(".") || entry.name === "node_modules") continue;
        
        const fullPath = path.join(currentDir, entry.name);
        const item = {
          name: entry.name,
          path: fullPath,
          isDirectory: entry.isDirectory(),
        };
        
        if (entry.isDirectory()) {
          item.children = await walk(fullPath, depth + 1);
        }
        
        result.push(item);
      }
      
      return result;
    }
    
    const tree = await walk(dir, 0);
    return { tag: "Right", value: tree };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
