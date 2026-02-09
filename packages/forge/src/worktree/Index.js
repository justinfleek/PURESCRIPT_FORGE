// Forge.Worktree.Index FFI
// 1:1 parity with opencode-dev/packages/opencode/src/worktree/index.ts

const { execSync } = require("child_process");

function parseWorktreeList(output) {
  const lines = output.split("\n");
  const worktrees = [];
  let current = null;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (line.startsWith("worktree ")) {
      if (current) worktrees.push(current);
      current = { path: line.substring(9).trim(), branch: "", isMain: false };
    } else if (line.startsWith("HEAD ") && current) {
      const head = line.substring(5).trim();
      const branchMatch = head.match(/refs\/heads\/(.+)/);
      current.branch = branchMatch ? branchMatch[1] : head;
    } else if (line.startsWith("branch ") && current) {
      const ref = line.substring(7).trim();
      const m = ref.match(/refs\/heads\/(.+)/);
      current.branch = m ? m[1] : ref;
    } else if (line.startsWith("bare") && current) {
      current.isMain = true;
    }
  }
  if (current) worktrees.push(current);
  return worktrees;
}

export const listWorktrees = () =>
  new Promise((resolve) => {
    try {
      const output = execSync("git worktree list --porcelain", { encoding: "utf-8" });
      resolve({ tag: "Right", value: parseWorktreeList(output) });
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Failed to list worktrees" });
    }
  });

export const createWorktree = (worktreePath) => (branch) => () =>
  new Promise((resolve) => {
    try {
      execSync(`git worktree add ${worktreePath} ${branch}`, { encoding: "utf-8" });
      resolve({ tag: "Right", value: { path: worktreePath, branch, isMain: false } });
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Failed to create worktree" });
    }
  });

export const removeWorktree = (worktreePath) => () =>
  new Promise((resolve) => {
    try {
      execSync(`git worktree remove ${worktreePath}`, { encoding: "utf-8" });
      resolve({ tag: "Right", value: null });
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Failed to remove worktree" });
    }
  });
