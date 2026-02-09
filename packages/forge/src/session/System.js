// FFI for Forge.Session.System
// 1:1 parity with opencode-dev/packages/opencode/src/session/system.ts

import { Ripgrep } from "../file/Ripgrep.js";
import { Instance } from "../project/Instance.js";

// Provider-specific system prompts
const PROMPT_ANTHROPIC = [
  "You are an expert software engineer. You communicate with maximum information density.",
  "You deliver direct, technically accurate responses without unnecessary elaboration.",
  "Use available tools to read files, search code, and execute commands as needed.",
  "Always read files before modifying them. Trace imports and dependencies.",
  "Prefer editing existing files over creating new ones.",
].join("\n");

const PROMPT_ANTHROPIC_WITHOUT_TODO = [
  "You are an expert software engineer. You communicate with maximum information density.",
  "You deliver direct, technically accurate responses without unnecessary elaboration.",
  "Use available tools to read files, search code, and execute commands as needed.",
  "Always read files before modifying them.",
].join("\n");

const PROMPT_BEAST = [
  "You are an expert software engineer with deep knowledge of programming languages and systems.",
  "You write clean, efficient code and provide precise technical explanations.",
  "Use tools to explore the codebase and verify your understanding before making changes.",
].join("\n");

const PROMPT_GEMINI = [
  "You are an expert software engineer. Provide clear, direct responses.",
  "Use tools to read and understand code before making modifications.",
  "Always verify your changes compile and pass tests.",
].join("\n");

const PROMPT_CODEX = [
  "You are an expert software engineer. You communicate concisely and precisely.",
  "You use available tools to read, search, and modify code.",
  "Always read the full file before making changes.",
  "Trace dependencies upstream and downstream before modifications.",
].join("\n");

export const instructions = PROMPT_CODEX.trim();

export const provider = (model) => () => {
  if (model.api.id.includes("gpt-5")) return [PROMPT_CODEX];
  if (model.api.id.includes("gpt-") || model.api.id.includes("o1") || model.api.id.includes("o3"))
    return [PROMPT_BEAST];
  if (model.api.id.includes("gemini-")) return [PROMPT_GEMINI];
  if (model.api.id.includes("claude")) return [PROMPT_ANTHROPIC];
  return [PROMPT_ANTHROPIC_WITHOUT_TODO];
};

export const environment = (model) => async () => {
  const project = Instance.project;
  let fileTree = "";

  // Generate file tree for git repos
  if (project.vcs === "git") {
    try {
      fileTree = await Ripgrep.tree({
        cwd: Instance.directory,
        limit: 200,
      });
    } catch (e) {
      fileTree = "(file tree unavailable)";
    }
  }

  const parts = [
    `You are powered by the model named ${model.api.id}. The exact model ID is ${model.providerID}/${model.api.id}`,
    `Here is some useful information about the environment you are running in:`,
    `<env>`,
    `  Working directory: ${Instance.directory}`,
    `  Is directory a git repo: ${project.vcs === "git" ? "yes" : "no"}`,
    `  Platform: ${process.platform}`,
    `  Today's date: ${new Date().toDateString()}`,
    `</env>`,
  ];

  if (fileTree) {
    parts.push(`<files>`);
    parts.push(`  ${fileTree}`);
    parts.push(`</files>`);
  }

  return [parts.join("\n")];
};
