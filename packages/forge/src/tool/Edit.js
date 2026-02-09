// FFI for Forge.Tool.Edit
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/edit.ts

import * as path from "path";
import { createTwoFilesPatch, diffLines } from "diff";
import { File } from "../file/Index.js";
import { FileWatcher } from "../file/Watcher.js";
import { Bus } from "../bus/Index.js";
import { FileTime } from "../file/Time.js";
import { Filesystem } from "../util/Filesystem.js";
import { Instance } from "../project/Instance.js";
import { Snapshot } from "../snapshot/Index.js";
import { assertExternalDirectory } from "./ExternalDirectory.js";
import { LSP } from "../lsp/Index.js";

const MAX_DIAGNOSTICS_PER_FILE = 20;

function normalizeLineEndings(text) {
  return text.replaceAll("\r\n", "\n");
}

export const execute = (params) => (ctx) => async () => {
  if (!params.filePath) {
    throw new Error("filePath is required");
  }

  if (params.oldString === params.newString) {
    throw new Error("oldString and newString must be different");
  }

  const filePath = path.isAbsolute(params.filePath) ? params.filePath : path.join(Instance.directory, params.filePath);
  await assertExternalDirectory(ctx)(filePath)(null)();

  let diff = "";
  let contentOld = "";
  let contentNew = "";
  
  await FileTime.withLock(filePath, async () => {
    if (params.oldString === "") {
      const existed = await Bun.file(filePath).exists();
      contentNew = params.newString;
      diff = trimDiff(createTwoFilesPatch(filePath, filePath, contentOld, contentNew));
      await ctx.ask({
        permission: "edit",
        patterns: [path.relative(Instance.worktree, filePath)],
        always: ["*"],
        metadata: {
          filepath: filePath,
          diff,
        },
      })();
      await Bun.write(filePath, params.newString);
      await Bus.publish(File.Event.Edited, { file: filePath });
      await Bus.publish(FileWatcher.Event.Updated, {
        file: filePath,
        event: existed ? "change" : "add",
      });
      FileTime.read(ctx.sessionID, filePath);
      return;
    }

    const file = Bun.file(filePath);
    const stats = await file.stat().catch(() => {});
    if (!stats) throw new Error(`File ${filePath} not found`);
    if (stats.isDirectory()) throw new Error(`Path is a directory, not a file: ${filePath}`);
    await FileTime.assert(ctx.sessionID, filePath);
    contentOld = await file.text();
    contentNew = replace(contentOld)(params.oldString)(params.newString)(params.replaceAll || false);

    diff = trimDiff(
      createTwoFilesPatch(filePath, filePath, normalizeLineEndings(contentOld), normalizeLineEndings(contentNew))
    );
    await ctx.ask({
      permission: "edit",
      patterns: [path.relative(Instance.worktree, filePath)],
      always: ["*"],
      metadata: {
        filepath: filePath,
        diff,
      },
    })();

    await file.write(contentNew);
    await Bus.publish(File.Event.Edited, { file: filePath });
    await Bus.publish(FileWatcher.Event.Updated, {
      file: filePath,
      event: "change",
    });
    contentNew = await file.text();
    diff = trimDiff(
      createTwoFilesPatch(filePath, filePath, normalizeLineEndings(contentOld), normalizeLineEndings(contentNew))
    );
    FileTime.read(ctx.sessionID, filePath);
  });

  const filediff = {
    file: filePath,
    before: contentOld,
    after: contentNew,
    additions: 0,
    deletions: 0,
  };
  for (const change of diffLines(contentOld, contentNew)) {
    if (change.added) filediff.additions += change.count || 0;
    if (change.removed) filediff.deletions += change.count || 0;
  }

  ctx.metadata({
    metadata: {
      diff,
      filediff,
      diagnostics: {},
    },
  })();

  let output = "Edit applied successfully.";
  await LSP.touchFile(filePath, true);
  const diagnostics = await LSP.diagnostics();
  const normalizedFilePath = Filesystem.normalizePath(filePath);
  const issues = diagnostics[normalizedFilePath] ?? [];
  const errors = issues.filter((item) => item.severity === 1);
  if (errors.length > 0) {
    const limited = errors.slice(0, MAX_DIAGNOSTICS_PER_FILE);
    const suffix =
      errors.length > MAX_DIAGNOSTICS_PER_FILE ? `\n... and ${errors.length - MAX_DIAGNOSTICS_PER_FILE} more` : "";
    output += `\n\nLSP errors detected in this file, please fix:\n<diagnostics file="${filePath}">\n${limited.map(LSP.Diagnostic.pretty).join("\n")}${suffix}\n</diagnostics>`;
  }

  return {
    metadata: {
      diagnostics,
      diff,
      filediff,
    },
    title: `${path.relative(Instance.worktree, filePath)}`,
    output,
  };
};

// Levenshtein distance
function levenshtein(a, b) {
  if (a === "" || b === "") {
    return Math.max(a.length, b.length);
  }
  const matrix = Array.from({ length: a.length + 1 }, (_, i) =>
    Array.from({ length: b.length + 1 }, (_, j) => (i === 0 ? j : j === 0 ? i : 0))
  );

  for (let i = 1; i <= a.length; i++) {
    for (let j = 1; j <= b.length; j++) {
      const cost = a[i - 1] === b[j - 1] ? 0 : 1;
      matrix[i][j] = Math.min(matrix[i - 1][j] + 1, matrix[i][j - 1] + 1, matrix[i - 1][j - 1] + cost);
    }
  }
  return matrix[a.length][b.length];
}

// Replacer generators
function* SimpleReplacer(_content, find) {
  yield find;
}

function* LineTrimmedReplacer(content, find) {
  const originalLines = content.split("\n");
  const searchLines = find.split("\n");

  if (searchLines[searchLines.length - 1] === "") {
    searchLines.pop();
  }

  for (let i = 0; i <= originalLines.length - searchLines.length; i++) {
    let matches = true;

    for (let j = 0; j < searchLines.length; j++) {
      const originalTrimmed = originalLines[i + j].trim();
      const searchTrimmed = searchLines[j].trim();

      if (originalTrimmed !== searchTrimmed) {
        matches = false;
        break;
      }
    }

    if (matches) {
      let matchStartIndex = 0;
      for (let k = 0; k < i; k++) {
        matchStartIndex += originalLines[k].length + 1;
      }

      let matchEndIndex = matchStartIndex;
      for (let k = 0; k < searchLines.length; k++) {
        matchEndIndex += originalLines[i + k].length;
        if (k < searchLines.length - 1) {
          matchEndIndex += 1;
        }
      }

      yield content.substring(matchStartIndex, matchEndIndex);
    }
  }
}

function* BlockAnchorReplacer(content, find) {
  const originalLines = content.split("\n");
  const searchLines = find.split("\n");

  if (searchLines.length < 3) {
    return;
  }

  if (searchLines[searchLines.length - 1] === "") {
    searchLines.pop();
  }

  const firstLineSearch = searchLines[0].trim();
  const lastLineSearch = searchLines[searchLines.length - 1].trim();

  const candidates = [];
  for (let i = 0; i < originalLines.length; i++) {
    if (originalLines[i].trim() !== firstLineSearch) {
      continue;
    }

    for (let j = i + 2; j < originalLines.length; j++) {
      if (originalLines[j].trim() === lastLineSearch) {
        candidates.push({ startLine: i, endLine: j });
        break;
      }
    }
  }

  if (candidates.length === 0) {
    return;
  }

  if (candidates.length === 1) {
    const { startLine, endLine } = candidates[0];
    let matchStartIndex = 0;
    for (let k = 0; k < startLine; k++) {
      matchStartIndex += originalLines[k].length + 1;
    }
    let matchEndIndex = matchStartIndex;
    for (let k = startLine; k <= endLine; k++) {
      matchEndIndex += originalLines[k].length;
      if (k < endLine) {
        matchEndIndex += 1;
      }
    }
    yield content.substring(matchStartIndex, matchEndIndex);
    return;
  }
}

function* MultiOccurrenceReplacer(content, find) {
  let startIndex = 0;
  while (true) {
    const index = content.indexOf(find, startIndex);
    if (index === -1) break;
    yield find;
    startIndex = index + find.length;
  }
}

export const trimDiff = (diff) => {
  const lines = diff.split("\n");
  const contentLines = lines.filter(
    (line) =>
      (line.startsWith("+") || line.startsWith("-") || line.startsWith(" ")) &&
      !line.startsWith("---") &&
      !line.startsWith("+++")
  );

  if (contentLines.length === 0) return diff;

  let min = Infinity;
  for (const line of contentLines) {
    const content = line.slice(1);
    if (content.trim().length > 0) {
      const match = content.match(/^(\s*)/);
      if (match) min = Math.min(min, match[1].length);
    }
  }
  if (min === Infinity || min === 0) return diff;
  const trimmedLines = lines.map((line) => {
    if (
      (line.startsWith("+") || line.startsWith("-") || line.startsWith(" ")) &&
      !line.startsWith("---") &&
      !line.startsWith("+++")
    ) {
      const prefix = line[0];
      const content = line.slice(1);
      return prefix + content.slice(min);
    }
    return line;
  });

  return trimmedLines.join("\n");
};

export const replace = (content) => (oldString) => (newString) => (replaceAll) => {
  if (oldString === newString) {
    throw new Error("oldString and newString must be different");
  }

  let notFound = true;

  for (const replacer of [
    SimpleReplacer,
    LineTrimmedReplacer,
    BlockAnchorReplacer,
    MultiOccurrenceReplacer,
  ]) {
    for (const search of replacer(content, oldString)) {
      const index = content.indexOf(search);
      if (index === -1) continue;
      notFound = false;
      if (replaceAll) {
        return content.replaceAll(search, newString);
      }
      const lastIndex = content.lastIndexOf(search);
      if (index !== lastIndex) continue;
      return content.substring(0, index) + newString + content.substring(index + search.length);
    }
  }

  if (notFound) {
    throw new Error("oldString not found in content");
  }
  throw new Error(
    "Found multiple matches for oldString. Provide more surrounding lines in oldString to identify the correct match."
  );
};
