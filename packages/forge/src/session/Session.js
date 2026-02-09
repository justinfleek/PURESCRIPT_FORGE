// FFI for Forge.Session.Session
// 1:1 parity with opencode-dev/packages/opencode/src/session/index.ts

import path from "path";
import { Slug } from "../util/Slug.js";
import { Bus } from "../bus/Index.js";
import { Storage } from "../storage/Storage.js";
import { Log } from "../util/Log.js";
import { MessageV2 } from "./MessageV2.js";

// Lazy imports to avoid circular dependencies
let Identifier, Instance, Installation, Config, Flag, Global, PermissionNext;

async function ensureImports() {
  if (!Identifier) {
    const [id, inst, install, config, flag, global, perm] = await Promise.all([
      import("../id/Id.js"),
      import("../project/Instance.js").catch(() => ({})),
      import("../installation/Index.js").catch(() => ({})),
      import("../config/Config.js").catch(() => ({})),
      import("../flag/Flag.js").catch(() => ({})),
      import("../global/Index.js").catch(() => ({})),
      import("../permission/Next.js").catch(() => ({})),
    ]);
    Identifier = id.Identifier;
    Instance = inst.Instance || { project: { id: "default" }, directory: process.cwd(), worktree: process.cwd() };
    Installation = install.Installation || { VERSION: "0.0.0" };
    Config = config.Config || { get: async () => ({}) };
    Flag = flag.Flag || {};
    Global = global.Global || { Path: { data: process.cwd() } };
    PermissionNext = perm.PermissionNext || {};
  }
}

const log = Log.create({ service: "session" });

const parentTitlePrefix = "New session - ";
const childTitlePrefix = "Child session - ";

function createDefaultTitle(isChild = false) {
  return (isChild ? childTitlePrefix : parentTitlePrefix) + new Date().toISOString();
}

export const isDefaultTitle = (title) => {
  return new RegExp(
    `^(${parentTitlePrefix}|${childTitlePrefix})\\d{4}-\\d{2}-\\d{2}T\\d{2}:\\d{2}:\\d{2}\\.\\d{3}Z$`
  ).test(title);
};

function getForkedTitle(title) {
  const match = title.match(/^(.+) \(fork #(\d+)\)$/);
  if (match) {
    const base = match[1];
    const num = parseInt(match[2], 10);
    return `${base} (fork #${num + 1})`;
  }
  return `${title} (fork #1)`;
}

// Bus Events
export const Event = {
  Created: {
    type: "session.created",
    publish: (payload) => Bus.publish("session.created", payload),
  },
  Updated: {
    type: "session.updated",
    publish: (payload) => Bus.publish("session.updated", payload),
  },
  Deleted: {
    type: "session.deleted", 
    publish: (payload) => Bus.publish("session.deleted", payload),
  },
  Diff: {
    type: "session.diff",
    publish: (payload) => Bus.publish("session.diff", payload),
  },
  Error: {
    type: "session.error",
    publish: (payload) => Bus.publish("session.error", payload),
  },
};

// Create a new session
export const create = (input) => async () => {
  try {
    await ensureImports();
    const result = await createNext({
      parentID: input?.parentID,
      directory: Instance.directory,
      title: input?.title,
      permission: input?.permission,
    });
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export async function createNext(input) {
  await ensureImports();
  const result = {
    id: Identifier.descending("session", input.id),
    slug: Slug.create(),
    version: Installation?.VERSION || "0.0.0",
    projectID: Instance?.project?.id || "default",
    directory: input.directory,
    parentID: input.parentID,
    title: input.title ?? createDefaultTitle(!!input.parentID),
    permission: input.permission,
    time: {
      created: Date.now(),
      updated: Date.now(),
    },
  };
  log.info("created", result);
  await Storage.write(["session", result.projectID, result.id], result);
  Bus.publish(Event.Created.type, { info: result });
  
  const cfg = await Config?.get?.() || {};
  if (!result.parentID && (Flag?.OPENCODE_AUTO_SHARE || cfg.share === "auto")) {
    // Auto-share is handled asynchronously
    share(result.id)().catch(() => {
      // Silently ignore sharing errors during session creation
    });
  }
  
  Bus.publish(Event.Updated.type, { info: result });
  return result;
}

// Fork a session
export const fork = (input) => async () => {
  try {
    await ensureImports();
    const original = await get(input.sessionID)();
    if (!original.value) throw new Error("session not found");
    
    const title = getForkedTitle(original.value.title);
    const session = await createNext({
      directory: Instance?.directory || process.cwd(),
      title,
    });
    
    const msgs = await messages({ sessionID: input.sessionID })();
    const idMap = new Map();

    for (const msg of msgs.value || []) {
      if (input.messageID && msg.info.id >= input.messageID) break;
      const newID = Identifier.ascending("message");
      idMap.set(msg.info.id, newID);

      const parentID = msg.info.role === "assistant" && msg.info.parentID 
        ? idMap.get(msg.info.parentID) 
        : undefined;
      
      const cloned = await updateMessage({
        ...msg.info,
        sessionID: session.id,
        id: newID,
        ...(parentID && { parentID }),
      })();

      for (const part of msg.parts) {
        await updatePart({
          ...part,
          id: Identifier.ascending("part"),
          messageID: cloned.value.id,
          sessionID: session.id,
        })();
      }
    }
    return { tag: "Right", value: session };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Touch session (update timestamp)
export const touch = (sessionID) => async () => {
  try {
    await update(sessionID, (draft) => {
      draft.time.updated = Date.now();
    })();
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get session plan path (sync version requires pre-loaded imports)
export const plan = (session) => {
  // Use safe defaults if imports not loaded
  const base = Instance?.project?.vcs
    ? path.join(Instance?.worktree || process.cwd(), ".opencode", "plans")
    : path.join(Global?.Path?.data || path.join(process.cwd(), ".opencode"), "plans");
  return path.join(base, [session.time.created, session.slug].join("-") + ".md");
};

// Get session by ID
export const get = (sessionID) => async () => {
  try {
    await ensureImports();
    const projectId = Instance?.project?.id || "default";
    const read = await Storage.read(["session", projectId, sessionID]);
    return { tag: "Right", value: read };
  } catch (err) {
    if (err.name === "NotFoundError") {
      return { tag: "Right", value: null };
    }
    return { tag: "Left", value: err.message };
  }
};

// Get session share info
export const getShare = (sessionID) => async () => {
  try {
    const read = await Storage.read(["share", sessionID]);
    return { tag: "Right", value: read };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Share session
export const share = (sessionID) => async () => {
  try {
    await ensureImports();
    const cfg = await Config?.get?.() || {};
    if (cfg.share === "disabled") {
      throw new Error("Sharing is disabled in configuration");
    }
    const { ShareNext } = await import("../share/ShareNext.js");
    const shareResult = await ShareNext.create(sessionID);
    await updateSession(sessionID, (draft) => {
      draft.share = {
        url: shareResult.url,
      };
    }, { touch: false });
    return { tag: "Right", value: shareResult };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Unshare session
export const unshare = (sessionID) => async () => {
  try {
    const { ShareNext } = await import("../share/ShareNext.js");
    await ShareNext.remove(sessionID);
    await updateSession(sessionID, (draft) => {
      draft.share = undefined;
    }, { touch: false });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Internal update helper (non-curried for internal use)
async function updateSession(sessionID, editor, options = {}) {
  await ensureImports();
  const projectId = Instance?.project?.id || "default";
  const result = await Storage.update(["session", projectId, sessionID], (draft) => {
    editor(draft);
    if (options?.touch !== false) {
      draft.time.updated = Date.now();
    }
  });
  Bus.publish(Event.Updated.type, { info: result });
  return result;
}

// Update session (PureScript FFI - curried)
export const update = (sessionID) => (editor) => (options) => async () => {
  try {
    const result = await updateSession(sessionID, editor, options);
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get session diff
export const diff = (sessionID) => async () => {
  try {
    const diffs = await Storage.read(["session_diff", sessionID]);
    return { tag: "Right", value: diffs ?? [] };
  } catch (err) {
    return { tag: "Right", value: [] };
  }
};

// Get session messages
export const messages = (input) => async () => {
  try {
    const result = [];
    for await (const msg of MessageV2.stream(input.sessionID)) {
      if (input.limit && result.length >= input.limit) break;
      result.push(msg);
    }
    result.reverse();
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List all sessions
export const list = async function* () {
  await ensureImports();
  const projectId = Instance?.project?.id || "default";
  for (const item of await Storage.list(["session", projectId])) {
    yield Storage.read(item);
  }
};

// List sessions (as array for PureScript FFI)
export const listFFI = async () => {
  try {
    await ensureImports();
    const result = [];
    for await (const session of list()) {
      result.push(session);
    }
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get children sessions
export const children = (parentID) => async () => {
  try {
    await ensureImports();
    const projectId = Instance?.project?.id || "default";
    const result = [];
    for (const item of await Storage.list(["session", projectId])) {
      const session = await Storage.read(item);
      if (session.parentID !== parentID) continue;
      result.push(session);
    }
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Remove session
export const remove = (sessionID) => async () => {
  try {
    await ensureImports();
    const projectId = Instance?.project?.id || "default";
    const session = await get(sessionID)();
    if (!session.value) {
      return { tag: "Right", value: undefined };
    }
    
    // Remove children recursively
    const childrenResult = await children(sessionID)();
    for (const child of childrenResult.value || []) {
      await remove(child.id)();
    }
    
    // Unshare if shared
    await unshare(sessionID)().catch(() => {});
    
    // Remove messages and parts
    for (const msg of await Storage.list(["message", sessionID])) {
      for (const part of await Storage.list(["part", msg.at(-1)])) {
        await Storage.remove(part);
      }
      await Storage.remove(msg);
    }
    
    await Storage.remove(["session", projectId, sessionID]);
    Bus.publish(Event.Deleted.type, { info: session.value });
    
    return { tag: "Right", value: undefined };
  } catch (err) {
    log.error("remove session error", { error: err });
    return { tag: "Left", value: err.message };
  }
};

// Update message
export const updateMessage = (msg) => async () => {
  try {
    await Storage.write(["message", msg.sessionID, msg.id], msg);
    Bus.publish(MessageV2.Event.Updated.type, { info: msg });
    return { tag: "Right", value: msg };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Remove message
export const removeMessage = (input) => async () => {
  try {
    await Storage.remove(["message", input.sessionID, input.messageID]);
    Bus.publish(MessageV2.Event.Removed.type, {
      sessionID: input.sessionID,
      messageID: input.messageID,
    });
    return { tag: "Right", value: input.messageID };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Remove part
export const removePart = (input) => async () => {
  try {
    await Storage.remove(["part", input.messageID, input.partID]);
    Bus.publish(MessageV2.Event.PartRemoved.type, {
      sessionID: input.sessionID,
      messageID: input.messageID,
      partID: input.partID,
    });
    return { tag: "Right", value: input.partID };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Update part
export const updatePart = (input) => async () => {
  try {
    const part = "delta" in input ? input.part : input;
    const delta = "delta" in input ? input.delta : undefined;
    await Storage.write(["part", part.messageID, part.id], part);
    Bus.publish(MessageV2.Event.PartUpdated.type, { part, delta });
    return { tag: "Right", value: part };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Calculate usage/cost (simplified without Decimal.js dependency)
export const getUsage = (input) => {
  const cacheReadInputTokens = input.usage?.cachedInputTokens ?? 0;
  const cacheWriteInputTokens = 
    input.metadata?.["anthropic"]?.["cacheCreationInputTokens"] ??
    input.metadata?.["bedrock"]?.["usage"]?.["cacheWriteInputTokens"] ??
    input.metadata?.["venice"]?.["usage"]?.["cacheCreationInputTokens"] ??
    0;

  const excludesCachedTokens = !!(input.metadata?.["anthropic"] || input.metadata?.["bedrock"]);
  const adjustedInputTokens = excludesCachedTokens
    ? (input.usage?.inputTokens ?? 0)
    : (input.usage?.inputTokens ?? 0) - cacheReadInputTokens - cacheWriteInputTokens;
  
  const safe = (value) => {
    if (!Number.isFinite(value)) return 0;
    return value;
  };

  const tokens = {
    input: safe(adjustedInputTokens),
    output: safe(input.usage?.outputTokens ?? 0),
    reasoning: safe(input.usage?.reasoningTokens ?? 0),
    cache: {
      write: safe(cacheWriteInputTokens),
      read: safe(cacheReadInputTokens),
    },
  };

  const costInfo =
    input.model?.cost?.experimentalOver200K && tokens.input + tokens.cache.read > 200_000
      ? input.model.cost.experimentalOver200K
      : input.model?.cost;
  
  // Calculate cost without Decimal.js (use simple arithmetic)
  const cost = safe(
    (tokens.input * (costInfo?.input ?? 0) / 1_000_000) +
    (tokens.output * (costInfo?.output ?? 0) / 1_000_000) +
    (tokens.cache.read * (costInfo?.cache?.read ?? 0) / 1_000_000) +
    (tokens.cache.write * (costInfo?.cache?.write ?? 0) / 1_000_000) +
    (tokens.reasoning * (costInfo?.output ?? 0) / 1_000_000)
  );
  
  return { cost, tokens };
};

// BusyError class
export class BusyError extends Error {
  constructor(sessionID) {
    super(`Session ${sessionID} is busy`);
    this.sessionID = sessionID;
    this.name = "BusyError";
  }
}

// Initialize session
export const initialize = (input) => async () => {
  try {
    const { SessionPrompt } = await import("./Prompt.js");
    await SessionPrompt.command({
      sessionID: input.sessionID,
      messageID: input.messageID,
      model: input.providerID + "/" + input.modelID,
      command: "init",
      arguments: "",
    });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
