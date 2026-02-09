// FFI for Forge.Tool.ExternalDirectory
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/external-directory.ts

import path from "path";
import { Instance } from "../project/Instance.js";

export const assertExternalDirectory = (ctx) => (target) => (options) => async () => {
  if (!target) return;

  if (options?.bypass) return;

  if (Instance.containsPath(target)) return;

  const kind = options?.kind ?? "file";
  const parentDir = kind === "directory" ? target : path.dirname(target);
  const glob = path.join(parentDir, "*");

  await ctx.ask({
    permission: "external_directory",
    patterns: [glob],
    always: [glob],
    metadata: {
      filepath: target,
      parentDir,
    },
  })();
};
