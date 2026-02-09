// FFI for Forge.Util.Filesystem
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/filesystem.ts

import { realpathSync } from "fs";
import { dirname, join, relative } from "path";

export const exists = (p) => () =>
  Bun.file(p)
    .stat()
    .then(() => true)
    .catch(() => false);

export const isDir = (p) => () =>
  Bun.file(p)
    .stat()
    .then((s) => s.isDirectory())
    .catch(() => false);

/**
 * On Windows, normalize a path to its canonical casing using the filesystem.
 * This is needed because Windows paths are case-insensitive but LSP servers
 * may return paths with different casing than what we send them.
 */
export const normalizePath = (p) => {
  if (process.platform !== "win32") return p;
  try {
    return realpathSync.native(p);
  } catch {
    return p;
  }
};

export const overlaps = (a) => (b) => {
  const relA = relative(a, b);
  const relB = relative(b, a);
  return !relA || !relA.startsWith("..") || !relB || !relB.startsWith("..");
};

export const contains = (parent) => (child) => {
  return !relative(parent, child).startsWith("..");
};

export const findUp = (target) => (start) => (stop) => async () => {
  let current = start;
  const result = [];
  while (true) {
    const search = join(current, target);
    if (await exists(search)()) result.push(search);
    if (stop === current) break;
    const parent = dirname(current);
    if (parent === current) break;
    current = parent;
  }
  return result;
};

export const up = (options) => async () => {
  const { targets, start, stop } = options;
  let current = start;
  const result = [];
  while (true) {
    for (const target of targets) {
      const search = join(current, target);
      if (await exists(search)()) result.push(search);
    }
    if (stop === current) break;
    const parent = dirname(current);
    if (parent === current) break;
    current = parent;
  }
  return result;
};

export const globUp = (pattern) => (start) => (stop) => async () => {
  let current = start;
  const result = [];
  while (true) {
    try {
      const glob = new Bun.Glob(pattern);
      for await (const match of glob.scan({
        cwd: current,
        absolute: true,
        onlyFiles: true,
        followSymlinks: true,
        dot: true,
      })) {
        result.push(match);
      }
    } catch {
      // Skip invalid glob patterns
    }
    if (stop === current) break;
    const parent = dirname(current);
    if (parent === current) break;
    current = parent;
  }
  return result;
};

// Filesystem namespace for JS consumers
export const Filesystem = {
  exists: async (p) => exists(p)(),
  isDir: async (p) => isDir(p)(),
  normalizePath,
  overlaps: (a, b) => overlaps(a)(b),
  contains: (parent, child) => contains(parent)(child),
  findUp: async (target, start, stop) => findUp(target)(start)(stop)(),
  up: async (options) => up(options)(),
  globUp: async (pattern, start, stop) => globUp(pattern)(start)(stop)(),
};
