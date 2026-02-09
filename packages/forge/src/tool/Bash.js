// FFI for Forge.Tool.Bash
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/bash.ts

import { spawn } from "child_process";
import path from "path";
import { $ } from "bun";
import { Instance } from "../project/Instance.js";
import { Shell } from "../shell/Shell.js";
import { Truncate } from "./Truncation.js";
import { defaultLogger as Log } from "../util/Log.js";
import { BashArity } from "../permission/Arity.js";

const MAX_METADATA_LENGTH = 30_000;
export const DEFAULT_TIMEOUT = 2 * 60 * 1000;

export const execute = (params) => (ctx) => async () => {
  const shell = Shell.acceptable();
  const cwd = params.workdir || Instance.directory;
  
  if (params.timeout !== undefined && params.timeout < 0) {
    throw new Error(`Invalid timeout value: ${params.timeout}. Timeout must be a positive number.`);
  }
  const timeout = params.timeout ?? DEFAULT_TIMEOUT;

  // Parse command for permission checking
  const directories = new Set();
  if (!Instance.containsPath(cwd)) directories.add(cwd);
  const patterns = new Set();
  const always = new Set();

  // Simplified permission handling
  patterns.add(params.command);
  always.add("*");

  if (directories.size > 0) {
    await ctx.ask({
      permission: "external_directory",
      patterns: Array.from(directories),
      always: Array.from(directories).map((x) => path.dirname(x) + "*"),
      metadata: {},
    })();
  }

  if (patterns.size > 0) {
    await ctx.ask({
      permission: "bash",
      patterns: Array.from(patterns),
      always: Array.from(always),
      metadata: {},
    })();
  }

  const proc = spawn(params.command, {
    shell,
    cwd,
    env: {
      ...process.env,
    },
    stdio: ["ignore", "pipe", "pipe"],
    detached: process.platform !== "win32",
  });

  let output = "";

  // Initialize metadata with empty output
  ctx.metadata({
    metadata: {
      output: "",
      description: params.description,
    },
  })();

  const append = (chunk) => {
    output += chunk.toString();
    ctx.metadata({
      metadata: {
        output: output.length > MAX_METADATA_LENGTH ? output.slice(0, MAX_METADATA_LENGTH) + "\n\n..." : output,
        description: params.description,
      },
    })();
  };

  proc.stdout?.on("data", append);
  proc.stderr?.on("data", append);

  let timedOut = false;
  let aborted = false;
  let exited = false;

  const kill = () => Shell.killTree(proc, { exited: () => exited });

  if (ctx.abort.aborted) {
    aborted = true;
    await kill();
  }

  const abortHandler = () => {
    aborted = true;
    void kill();
  };

  ctx.abort.addEventListener("abort", abortHandler, { once: true });

  const timeoutTimer = setTimeout(() => {
    timedOut = true;
    void kill();
  }, timeout + 100);

  await new Promise((resolve, reject) => {
    const cleanup = () => {
      clearTimeout(timeoutTimer);
      ctx.abort.removeEventListener("abort", abortHandler);
    };

    proc.once("exit", () => {
      exited = true;
      cleanup();
      resolve();
    });

    proc.once("error", (error) => {
      exited = true;
      cleanup();
      reject(error);
    });
  });

  const resultMetadata = [];

  if (timedOut) {
    resultMetadata.push(`bash tool terminated command after exceeding timeout ${timeout} ms`);
  }

  if (aborted) {
    resultMetadata.push("User aborted the command");
  }

  if (resultMetadata.length > 0) {
    output += "\n\n<bash_metadata>\n" + resultMetadata.join("\n") + "\n</bash_metadata>";
  }

  return {
    title: params.description,
    metadata: {
      output: output.length > MAX_METADATA_LENGTH ? output.slice(0, MAX_METADATA_LENGTH) + "\n\n..." : output,
      exit: proc.exitCode,
      description: params.description,
    },
    output,
  };
};
