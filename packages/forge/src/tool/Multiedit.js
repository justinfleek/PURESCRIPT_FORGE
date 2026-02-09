// FFI for Forge.Tool.Multiedit
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/multiedit.ts

import path from "path";
import { Instance } from "../project/Instance.js";
import { EditTool } from "./Edit.js";

export const execute = (params) => (ctx) => async () => {
  const tool = await EditTool.init();
  const results = [];
  for (const edit of params.edits) {
    const result = await tool.execute(
      {
        filePath: params.filePath,
        oldString: edit.oldString,
        newString: edit.newString,
        replaceAll: edit.replaceAll,
      },
      ctx
    );
    results.push(result);
  }
  return {
    title: path.relative(Instance.worktree, params.filePath),
    metadata: {
      results: results.map((r) => r.metadata),
    },
    output: results.at(-1)?.output ?? "",
  };
};
