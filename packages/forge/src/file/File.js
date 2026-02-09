// FFI for Forge.File.File

import fs from "fs/promises";
import path from "path";

export const read = (filepath) => async () => {
  try {
    const content = await fs.readFile(filepath, "utf-8");
    return { tag: "Right", value: content };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const write = (filepath) => (content) => async () => {
  try {
    await fs.mkdir(path.dirname(filepath), { recursive: true });
    await fs.writeFile(filepath, content, "utf-8");
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const exists = (filepath) => async () => {
  try {
    await fs.access(filepath);
    return true;
  } catch {
    return false;
  }
};

export const info = (filepath) => async () => {
  try {
    const stat = await fs.stat(filepath);
    return {
      tag: "Right",
      value: {
        path: filepath,
        name: path.basename(filepath),
        size: stat.size,
        isDirectory: stat.isDirectory(),
        modifiedAt: stat.mtimeMs,
      },
    };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const remove = (filepath) => async () => {
  try {
    await fs.unlink(filepath);
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const mkdir = (dirpath) => async () => {
  try {
    await fs.mkdir(dirpath, { recursive: true });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const readdir = (dirpath) => async () => {
  try {
    const entries = await fs.readdir(dirpath);
    return { tag: "Right", value: entries };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
