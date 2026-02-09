// FFI for Forge.Tool.Registry
// 1:1 parity with opencode-dev/packages/opencode/src/tool/registry.ts

import { Log } from "../util/Log.js";
import { Tool } from "./Tool.js";

const log = Log.create({ service: "tool.registry" });

// Built-in tools registry
const builtInTools = new Map();
const customTools = new Map();

// Initialize built-in tools
async function initBuiltInTools() {
  // Lazy load tool implementations
  const tools = [
    { id: "bash", loader: () => import("./Bash.js").then(m => m.BashTool) },
    { id: "read", loader: () => import("./Read.js").then(m => m.ReadTool) },
    { id: "write", loader: () => import("./Write.js").then(m => m.WriteTool) },
    { id: "edit", loader: () => import("./Edit.js").then(m => m.EditTool) },
    { id: "glob", loader: () => import("./Glob.js").then(m => m.GlobTool) },
    { id: "grep", loader: () => import("./Grep.js").then(m => m.GrepTool) },
    { id: "task", loader: () => import("./Task.js").then(m => m.TaskTool) },
    { id: "webfetch", loader: () => import("./WebFetch.js").then(m => m.WebFetchTool) },
    { id: "websearch", loader: () => import("./WebSearch.js").then(m => m.WebSearchTool) },
    { id: "codesearch", loader: () => import("./CodeSearch.js").then(m => m.CodeSearchTool) },
    { id: "question", loader: () => import("./Question.js").then(m => m.QuestionTool) },
    { id: "todowrite", loader: () => import("./Todo.js").then(m => m.TodoWriteTool) },
    { id: "todoread", loader: () => import("./Todo.js").then(m => m.TodoReadTool) },
    { id: "skill", loader: () => import("./Skill.js").then(m => m.SkillTool) },
    { id: "apply_patch", loader: () => import("./ApplyPatch.js").then(m => m.ApplyPatchTool) },
    { id: "plan_exit", loader: () => import("./Plan.js").then(m => m.PlanExitTool) },
    { id: "plan_enter", loader: () => import("./Plan.js").then(m => m.PlanEnterTool) },
  ];

  for (const { id, loader } of tools) {
    builtInTools.set(id, { id, loader, loaded: null });
  }
}

// Initialize on module load
initBuiltInTools().catch(console.error);

// Load a tool definition
async function loadTool(entry) {
  if (!entry.loaded) {
    try {
      entry.loaded = await entry.loader();
    } catch (err) {
      log.warn("failed to load tool", { id: entry.id, error: err.message });
      return null;
    }
  }
  return entry.loaded;
}

// Register a custom tool
export async function register(tool) {
  customTools.set(tool.id, { id: tool.id, loaded: tool });
}

// Get all tool IDs
export async function ids() {
  return [...builtInTools.keys(), ...customTools.keys()];
}

// Get tools for a model/agent
export async function tools(model, agent) {
  const result = [];
  const config = await import("../config/Config.js").then(m => m.Config.get());
  const { Flag } = await import("../flag/Flag.js").catch(() => ({ Flag: {} }));

  const allEntries = [...builtInTools.values(), ...customTools.values()];

  for (const entry of allEntries) {
    // Filter by feature flags
    if ((entry.id === "codesearch" || entry.id === "websearch")) {
      if (model.providerID !== "opencode" && !Flag.OPENCODE_ENABLE_EXA) {
        continue;
      }
    }

    // Use apply_patch for certain GPT models
    const usePatch =
      model.modelID.includes("gpt-") &&
      !model.modelID.includes("oss") &&
      !model.modelID.includes("gpt-4");
    
    if (entry.id === "apply_patch" && !usePatch) continue;
    if ((entry.id === "edit" || entry.id === "write") && usePatch) continue;

    // Filter by client
    if (entry.id === "question" && !["app", "cli", "desktop"].includes(Flag.OPENCODE_CLIENT)) {
      continue;
    }

    // Filter experimental tools
    if (entry.id === "lsp" && !Flag.OPENCODE_EXPERIMENTAL_LSP_TOOL) continue;
    if (config?.experimental?.batch_tool !== true && entry.id === "batch") continue;
    if ((entry.id === "plan_exit" || entry.id === "plan_enter")) {
      if (!Flag.OPENCODE_EXPERIMENTAL_PLAN_MODE || Flag.OPENCODE_CLIENT !== "cli") {
        continue;
      }
    }

    try {
      const tool = await loadTool(entry);
      if (tool) {
        const initCtx = { agent };
        const def = await tool.init(initCtx);
        result.push({
          id: entry.id,
          ...def,
        });
      }
    } catch (err) {
      log.warn("failed to init tool", { id: entry.id, error: err.message });
    }
  }

  return result;
}

// ToolRegistry namespace
export const ToolRegistry = {
  register,
  ids,
  tools,
};

// PureScript FFI exports
export const registerFFI = (tool) => () => register(tool);
export const idsFFI = async () => ids();
export const toolsFFI = (model) => (agent) => async () => {
  try {
    const result = await tools(model, agent);
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
