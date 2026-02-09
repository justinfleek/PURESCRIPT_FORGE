// FFI for Forge.Session.MessageV2
// 1:1 parity with opencode-dev/packages/opencode/src/session/message-v2.ts

import { Storage } from "../storage/Storage.js";
import { Identifier } from "../id/Id.js";
import { Bus } from "../bus/Index.js";

// Error types
export class OutputLengthError extends Error {
  constructor() {
    super("Output length exceeded");
    this.name = "MessageOutputLengthError";
  }
}

export class AbortedError extends Error {
  constructor(message) {
    super(message);
    this.name = "MessageAbortedError";
  }
}

export class AuthError extends Error {
  constructor(providerID, message) {
    super(message);
    this.name = "ProviderAuthError";
    this.providerID = providerID;
  }
}

export class APIError extends Error {
  constructor(data) {
    super(data.message);
    this.name = "APIError";
    this.statusCode = data.statusCode;
    this.isRetryable = data.isRetryable;
    this.responseHeaders = data.responseHeaders;
    this.responseBody = data.responseBody;
    this.metadata = data.metadata;
  }
}

// Bus Events
export const Event = {
  Updated: {
    type: "message.updated",
  },
  Removed: {
    type: "message.removed",
  },
  PartUpdated: {
    type: "message.part.updated",
  },
  PartRemoved: {
    type: "message.part.removed",
  },
};

// Stream messages for a session
export async function* stream(sessionID) {
  const list = await Array.fromAsync(await Storage.list(["message", sessionID]));
  for (let i = list.length - 1; i >= 0; i--) {
    yield await get({
      sessionID,
      messageID: list[i][2],
    });
  }
}

// Get parts for a message
export const parts = async (messageID) => {
  const result = [];
  for (const item of await Storage.list(["part", messageID])) {
    const read = await Storage.read(item);
    result.push(read);
  }
  result.sort((a, b) => (a.id > b.id ? 1 : -1));
  return result;
};

// Get message with parts
export const get = async (input) => {
  return {
    info: await Storage.read(["message", input.sessionID, input.messageID]),
    parts: await parts(input.messageID),
  };
};

// Filter compacted messages
export async function filterCompacted(stream) {
  const result = [];
  const completed = new Set();
  for await (const msg of stream) {
    result.push(msg);
    if (
      msg.info.role === "user" &&
      completed.has(msg.info.id) &&
      msg.parts.some((part) => part.type === "compaction")
    )
      break;
    if (msg.info.role === "assistant" && msg.info.summary && msg.info.finish)
      completed.add(msg.info.parentID);
  }
  result.reverse();
  return result;
}

// Convert error to message format
export function fromError(e, ctx) {
  if (e instanceof DOMException && e.name === "AbortError") {
    return {
      name: "MessageAbortedError",
      message: e.message,
    };
  }
  
  if (e instanceof OutputLengthError) {
    return {
      name: "MessageOutputLengthError",
      message: e.message,
    };
  }
  
  if (e.name === "LoadAPIKeyError") {
    return {
      name: "ProviderAuthError",
      providerID: ctx.providerID,
      message: e.message,
    };
  }
  
  if (e?.code === "ECONNRESET") {
    return {
      name: "APIError",
      message: "Connection reset by server",
      isRetryable: true,
      metadata: {
        code: e.code || "",
        syscall: e.syscall || "",
        message: e.message || "",
      },
    };
  }
  
  if (e.name === "APICallError" || e.isRetryable !== undefined) {
    return {
      name: "APIError",
      message: e.message || "Unknown error",
      statusCode: e.statusCode,
      isRetryable: e.isRetryable,
      responseHeaders: e.responseHeaders,
      responseBody: e.responseBody,
    };
  }
  
  if (e instanceof Error) {
    return {
      name: "Unknown",
      message: e.toString(),
    };
  }
  
  return {
    name: "Unknown",
    message: JSON.stringify(e),
  };
}

// Convert to model messages (simplified - full implementation in processor)
export function toModelMessages(input, model) {
  const result = [];
  
  for (const msg of input) {
    if (msg.parts.length === 0) continue;
    
    if (msg.info.role === "user") {
      const userMessage = {
        id: msg.info.id,
        role: "user",
        content: msg.parts
          .filter((part) => part.type === "text" && !part.ignored)
          .map((part) => part.text)
          .join("\n"),
      };
      result.push(userMessage);
    }
    
    if (msg.info.role === "assistant") {
      // Skip error messages without content
      if (msg.info.error && !msg.parts.some((part) => part.type !== "step-start" && part.type !== "reasoning")) {
        continue;
      }
      
      const assistantMessage = {
        id: msg.info.id,
        role: "assistant",
        content: msg.parts
          .filter((part) => part.type === "text")
          .map((part) => part.text)
          .join("\n"),
      };
      
      if (assistantMessage.content) {
        result.push(assistantMessage);
      }
    }
  }
  
  return result;
}

// Export namespace for direct usage
export const MessageV2 = {
  Event,
  stream,
  parts,
  get,
  filterCompacted,
  fromError,
  toModelMessages,
  OutputLengthError,
  AbortedError,
  AuthError,
  APIError,
};
