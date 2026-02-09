// FFI for Forge.Server.Routes.Session
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/session.ts

import * as Session from "../../session/Session.js";

// Create session
export const createFFI = (input) => async () => {
  try {
    const result = await Session.create(input)();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List sessions
export const listFFI = async () => {
  try {
    const result = await Session.listFFI();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get session
export const getFFI = (sessionID) => async () => {
  try {
    const result = await Session.get(sessionID)();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get messages
export const messagesFFI = (sessionID) => (limit) => async () => {
  try {
    const result = await Session.messages({ sessionID, limit })();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Send prompt
export const promptFFI = (sessionID) => (text) => async () => {
  try {
    const { SessionPrompt } = await import("../../session/Prompt.js");
    const result = await SessionPrompt.prompt({
      sessionID,
      parts: [{ type: "text", text }],
    });
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Execute command
export const commandFFI = (sessionID) => (command) => (args) => async () => {
  try {
    const { SessionPrompt } = await import("../../session/Prompt.js");
    const result = await SessionPrompt.command({
      sessionID,
      command,
      arguments: args,
    });
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Share session
export const shareFFI = (sessionID) => async () => {
  try {
    const result = await Session.share(sessionID)();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Unshare session
export const unshareFFI = (sessionID) => async () => {
  try {
    const result = await Session.unshare(sessionID)();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Delete session
export const deleteFFI = (sessionID) => async () => {
  try {
    const result = await Session.remove(sessionID)();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Fork session
export const forkFFI = (sessionID) => (messageID) => async () => {
  try {
    const result = await Session.fork({ sessionID, messageID })();
    return result;
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Abort session
export const abortFFI = (sessionID) => async () => {
  try {
    const { SessionPrompt } = await import("../../session/Prompt.js");
    SessionPrompt.cancel(sessionID);
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
