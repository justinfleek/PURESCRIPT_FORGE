// FFI for Forge.Tool.ApplyPatch
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/apply_patch.ts

import * as path from "path";
import * as fs from "fs/promises";
import { Bus } from "../bus/Index.js";
import { FileWatcher } from "../file/Watcher.js";
import { Instance } from "../project/Instance.js";
import { Patch } from "../patch/Index.js";
import { createTwoFilesPatch, diffLines } from "diff";
import { assertExternalDirectory } from "./ExternalDirectory.js";
import { trimDiff } from "./Edit.js";
import { LSP } from "../lsp/Index.js";
import { Filesystem } from "../util/Filesystem.js";
import { File } from "../file/Index.js";

export const execute = (params) => (ctx) => async () => {
  if (!params.patchText) {
    throw new Error("patchText is required");
  }

  // Parse the patch to get hunks
  let hunks;
  try {
    const parseResult = Patch.parsePatch(params.patchText);
    hunks = parseResult.hunks;
  } catch (error) {
    throw new Error(`apply_patch verification failed: ${error}`);
  }

  if (hunks.length === 0) {
    const normalized = params.patchText.replace(/\r\n/g, "\n").replace(/\r/g, "\n").trim();
    if (normalized === "*** Begin Patch\n*** End Patch") {
      throw new Error("patch rejected: empty patch");
    }
    throw new Error("apply_patch verification failed: no hunks found");
  }

  // Validate file paths and check permissions
  const fileChanges = [];
  let totalDiff = "";

  for (const hunk of hunks) {
    const filePath = path.resolve(Instance.directory, hunk.path);
    await assertExternalDirectory(ctx)(filePath)(null)();

    switch (hunk.type) {
      case "add": {
        const oldContent = "";
        const newContent =
          hunk.contents.length === 0 || hunk.contents.endsWith("\n") ? hunk.contents : `${hunk.contents}\n`;
        const diff = trimDiff(createTwoFilesPatch(filePath, filePath, oldContent, newContent));

        let additions = 0;
        let deletions = 0;
        for (const change of diffLines(oldContent, newContent)) {
          if (change.added) additions += change.count || 0;
          if (change.removed) deletions += change.count || 0;
        }

        fileChanges.push({
          filePath,
          oldContent,
          newContent,
          type: "add",
          diff,
          additions,
          deletions,
        });

        totalDiff += diff + "\n";
        break;
      }

      case "update": {
        const stats = await fs.stat(filePath).catch(() => null);
        if (!stats || stats.isDirectory()) {
          throw new Error(`apply_patch verification failed: Failed to read file to update: ${filePath}`);
        }

        const oldContent = await fs.readFile(filePath, "utf-8");
        let newContent = oldContent;

        try {
          const fileUpdate = Patch.deriveNewContentsFromChunks(filePath, hunk.chunks);
          newContent = fileUpdate.content;
        } catch (error) {
          throw new Error(`apply_patch verification failed: ${error}`);
        }

        const diff = trimDiff(createTwoFilesPatch(filePath, filePath, oldContent, newContent));

        let additions = 0;
        let deletions = 0;
        for (const change of diffLines(oldContent, newContent)) {
          if (change.added) additions += change.count || 0;
          if (change.removed) deletions += change.count || 0;
        }

        const movePath = hunk.move_path ? path.resolve(Instance.directory, hunk.move_path) : undefined;
        await assertExternalDirectory(ctx)(movePath)(null)();

        fileChanges.push({
          filePath,
          oldContent,
          newContent,
          type: hunk.move_path ? "move" : "update",
          movePath,
          diff,
          additions,
          deletions,
        });

        totalDiff += diff + "\n";
        break;
      }

      case "delete": {
        const contentToDelete = await fs.readFile(filePath, "utf-8").catch((error) => {
          throw new Error(`apply_patch verification failed: ${error}`);
        });
        const deleteDiff = trimDiff(createTwoFilesPatch(filePath, filePath, contentToDelete, ""));
        const deletions = contentToDelete.split("\n").length;

        fileChanges.push({
          filePath,
          oldContent: contentToDelete,
          newContent: "",
          type: "delete",
          diff: deleteDiff,
          additions: 0,
          deletions,
        });

        totalDiff += deleteDiff + "\n";
        break;
      }
    }
  }

  // Build per-file metadata for UI rendering
  const files = fileChanges.map((change) => ({
    filePath: change.filePath,
    relativePath: path.relative(Instance.worktree, change.movePath ?? change.filePath),
    type: change.type,
    diff: change.diff,
    before: change.oldContent,
    after: change.newContent,
    additions: change.additions,
    deletions: change.deletions,
    movePath: change.movePath,
  }));

  // Check permissions
  const relativePaths = fileChanges.map((c) => path.relative(Instance.worktree, c.filePath));
  await ctx.ask({
    permission: "edit",
    patterns: relativePaths,
    always: ["*"],
    metadata: {
      filepath: relativePaths.join(", "),
      diff: totalDiff,
      files,
    },
  })();

  // Apply the changes
  const updates = [];

  for (const change of fileChanges) {
    const edited = change.type === "delete" ? undefined : (change.movePath ?? change.filePath);
    switch (change.type) {
      case "add":
        await fs.mkdir(path.dirname(change.filePath), { recursive: true });
        await fs.writeFile(change.filePath, change.newContent, "utf-8");
        updates.push({ file: change.filePath, event: "add" });
        break;

      case "update":
        await fs.writeFile(change.filePath, change.newContent, "utf-8");
        updates.push({ file: change.filePath, event: "change" });
        break;

      case "move":
        if (change.movePath) {
          await fs.mkdir(path.dirname(change.movePath), { recursive: true });
          await fs.writeFile(change.movePath, change.newContent, "utf-8");
          await fs.unlink(change.filePath);
          updates.push({ file: change.filePath, event: "unlink" });
          updates.push({ file: change.movePath, event: "add" });
        }
        break;

      case "delete":
        await fs.unlink(change.filePath);
        updates.push({ file: change.filePath, event: "unlink" });
        break;
    }

    if (edited) {
      await Bus.publish(File.Event.Edited, { file: edited });
    }
  }

  // Publish file change events
  for (const update of updates) {
    await Bus.publish(FileWatcher.Event.Updated, update);
  }

  // Notify LSP and collect diagnostics
  for (const change of fileChanges) {
    if (change.type === "delete") continue;
    const target = change.movePath ?? change.filePath;
    await LSP.touchFile(target, true);
  }
  const diagnostics = await LSP.diagnostics();

  // Generate output summary
  const summaryLines = fileChanges.map((change) => {
    if (change.type === "add") {
      return `A ${path.relative(Instance.worktree, change.filePath)}`;
    }
    if (change.type === "delete") {
      return `D ${path.relative(Instance.worktree, change.filePath)}`;
    }
    const target = change.movePath ?? change.filePath;
    return `M ${path.relative(Instance.worktree, target)}`;
  });
  let output = `Success. Updated the following files:\n${summaryLines.join("\n")}`;

  // Report LSP errors
  const MAX_DIAGNOSTICS_PER_FILE = 20;
  for (const change of fileChanges) {
    if (change.type === "delete") continue;
    const target = change.movePath ?? change.filePath;
    const normalized = Filesystem.normalizePath(target);
    const issues = diagnostics[normalized] ?? [];
    const errors = issues.filter((item) => item.severity === 1);
    if (errors.length > 0) {
      const limited = errors.slice(0, MAX_DIAGNOSTICS_PER_FILE);
      const suffix =
        errors.length > MAX_DIAGNOSTICS_PER_FILE ? `\n... and ${errors.length - MAX_DIAGNOSTICS_PER_FILE} more` : "";
      output += `\n\nLSP errors detected in ${path.relative(Instance.worktree, target)}, please fix:\n<diagnostics file="${target}">\n${limited.map(LSP.Diagnostic.pretty).join("\n")}${suffix}\n</diagnostics>`;
    }
  }

  return {
    title: output,
    metadata: {
      diff: totalDiff,
      files,
      diagnostics,
    },
    output,
  };
};
