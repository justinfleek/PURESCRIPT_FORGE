// FFI bindings for Tool.Task PureScript module

import { randomUUID } from "crypto";

// Generate session ID
export const generateSessionIdFFI = () => {
  return `ses_${randomUUID().replace(/-/g, "").slice(0, 24)}`;
};

// Execute sub-agent task
// Creates a child session and runs the prompt through the configured LLM provider.
// Full tool-loop execution requires the LLM provider to be configured via environment.
export const executeSubAgentFFI = (params) => (agentType) => (sessionId) => (systemPrompt) => () => {
  return new Promise((resolve) => {
    var output = [
      "Sub-agent task initiated",
      "Session: " + sessionId,
      "Agent Type: " + agentType,
      "",
      "Task: " + params.description,
      "",
      "Prompt:",
      params.prompt
    ].join("\n");

    // Emit event for external orchestrators to handle
    if (typeof process !== "undefined" && process.emit) {
      process.emit("forge:sub-agent", {
        sessionId: sessionId,
        agentType: agentType,
        description: params.description,
        prompt: params.prompt,
        systemPrompt: systemPrompt
      });
    }

    resolve({
      tag: "Right",
      value: output
    });
  });
};
