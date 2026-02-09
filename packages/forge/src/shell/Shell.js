// Forge.Shell.Shell FFI
// 1:1 parity with opencode-dev/packages/opencode/src/shell/shell.ts

const path = require("path");
const { spawn } = require("child_process");

function fallback() {
  if (process.platform === "win32") {
    try {
      const { execSync } = require("child_process");
      const gitPath = execSync("where git", { encoding: "utf-8" }).trim();
      if (gitPath) {
        const bashPath = path.join(path.dirname(gitPath), "..", "bin", "bash.exe");
        const fs = require("fs");
        if (fs.existsSync(bashPath)) return bashPath;
      }
    } catch (_) {}
    return process.env.COMSPEC || "cmd.exe";
  }
  if (process.platform === "darwin") return "/bin/zsh";
  try {
    const { execSync } = require("child_process");
    const bash = execSync("which bash", { encoding: "utf-8" }).trim();
    if (bash) return bash;
  } catch (_) {}
  return "/bin/sh";
}

function getDefaultShell() {
  const s = process.env.SHELL;
  if (s) return s;
  return fallback();
}

function exec(command, cwd) {
  return new Promise((resolve) => {
    const shell = getDefaultShell();
    const opts = { shell: true };
    if (cwd != null) opts.cwd = cwd;
    const proc = spawn(shell, ["-c", command], opts);
    let stdout = "";
    let stderr = "";
    proc.stdout?.on("data", (d) => { stdout += d.toString(); });
    proc.stderr?.on("data", (d) => { stderr += d.toString(); });
    proc.on("close", (code) => {
      resolve({
        tag: "Right",
        value: { stdout, stderr, exitCode: code ?? 0 },
      });
    });
    proc.on("error", (err) => {
      resolve({ tag: "Left", value: err.message });
    });
  });
}

function escape(str) {
  return "'" + str.replace(/'/g, "'\\''") + "'";
}

export const getDefaultShellFFI = () => getDefaultShell();
export const execFFI = (command) => (cwd) => () => exec(command, cwd);
export const escapeFFI = (str) => escape(str);
