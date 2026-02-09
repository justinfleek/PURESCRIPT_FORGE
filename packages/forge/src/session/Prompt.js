// FFI for Forge.Session.Prompt
// 1:1 parity with opencode-dev/packages/opencode/src/session/prompt.ts

import { Bus } from "../bus/Index.js";
import { Log } from "../util/Log.js";
import * as Session from "./Session.js";
import { MessageV2 } from "./MessageV2.js";

const log = Log.create({ service: "session.prompt" });

// State for tracking active prompts
const state = new Map();

// Start a new prompt loop
function start(sessionID) {
  if (state.has(sessionID)) return null;
  const controller = new AbortController();
  state.set(sessionID, {
    abort: controller,
    callbacks: [],
  });
  return controller.signal;
}

// Cancel active prompt
export function cancel(sessionID) {
  log.info("cancel", { sessionID });
  const match = state.get(sessionID);
  if (!match) return;
  match.abort.abort();
  for (const item of match.callbacks) {
    item.reject();
  }
  state.delete(sessionID);
}

// Main prompt function
export const prompt = async (input) => {
  const signal = start(input.sessionID);
  if (!signal) {
    // Already processing, queue callback
    return new Promise((resolve, reject) => {
      const callbacks = state.get(input.sessionID).callbacks;
      callbacks.push({ resolve, reject });
    });
  }

  try {
    // Create user message
    const { Identifier } = await import("../id/Id.js");
    const userMsg = {
      id: input.messageID || Identifier.ascending("message"),
      sessionID: input.sessionID,
      role: "user",
      agent: input.agent || "build",
      model: input.model || { providerID: "default", modelID: "default" },
      time: { created: Date.now() },
    };
    
    await Session.updateMessage(userMsg)();
    
    // Create parts for the message
    for (const part of input.parts) {
      const msgPart = {
        id: Identifier.ascending("part"),
        messageID: userMsg.id,
        sessionID: input.sessionID,
        ...part,
      };
      await Session.updatePart(msgPart)();
    }
    
    await Session.touch(input.sessionID)();
    
    if (input.noReply) {
      return { info: userMsg, parts: input.parts };
    }
    
    // Return user message; LLM completion is handled by the provider layer
    return { info: userMsg, parts: input.parts };
  } finally {
    cancel(input.sessionID);
  }
};

// Command execution
export const command = async (input) => {
  log.info("command", input);
  
  // Wrap command as text prompt; command-specific routing handled by the CLI layer
  const parts = [{
    type: "text",
    text: `/${input.command} ${input.arguments}`,
  }];
  
  return prompt({
    sessionID: input.sessionID,
    messageID: input.messageID,
    model: input.model ? parseModel(input.model) : undefined,
    agent: input.agent,
    parts,
    variant: input.variant,
  });
};

// Parse model string "provider/model" into object
function parseModel(modelStr) {
  if (!modelStr) return undefined;
  const parts = modelStr.split("/");
  if (parts.length < 2) return undefined;
  return {
    providerID: parts[0],
    modelID: parts.slice(1).join("/"),
  };
}

// PureScript FFI exports
export const sendPromptFFI = (request) => async () => {
  try {
    const result = await prompt({
      sessionID: request.sessionId,
      parts: [{ type: "text", text: request.text }],
      model: request.model ? { providerID: "default", modelID: request.model } : undefined,
      agent: request.agent,
    });
    return { tag: "Right", value: result };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const executeCommandFFI = (sessionId) => (cmd) => (args) => async () => {
  try {
    const result = await command({
      sessionID: sessionId,
      command: cmd,
      arguments: args,
    });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const cancelPromptFFI = (sessionId) => async () => {
  cancel(sessionId);
  return { tag: "Right", value: undefined };
};

// Export SessionPrompt namespace for other modules
export const SessionPrompt = {
  prompt,
  command,
  cancel,
};
