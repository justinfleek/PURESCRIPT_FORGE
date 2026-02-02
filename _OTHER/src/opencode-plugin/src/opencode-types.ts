/**
 * Typed interfaces for OpenCode SDK integration
 * 
 * These types replace 'unknown' usage in FFI boundaries.
 * Based on @opencode-ai/plugin SDK types.
 */

/**
 * OpenCode Event - All possible event types from OpenCode SDK
 */
export type OpenCodeEvent =
  | FileChangedEvent
  | MessageCreatedEvent
  | StreamChunkEvent
  | MessageCompletedEvent
  | ToolExecuteEvent
  | SessionCreatedEvent
  | ConfigChangedEvent;

/**
 * File changed event
 */
export interface FileChangedEvent {
  type: "file.changed";
  path: string;
  content?: string;
  timestamp: Date;
}

/**
 * Message created event
 */
export interface MessageCreatedEvent {
  type: "message.created";
  message: {
    id: string;
    role: "user" | "assistant" | "system";
    content: string;
    timestamp: Date;
  };
  session: {
    id: string;
    model: string;
  };
}

/**
 * Stream chunk event
 */
export interface StreamChunkEvent {
  type: "stream.chunk";
  messageId: string;
  chunk: string;
  tokenCount?: number;
}

/**
 * Message completed event
 */
export interface MessageCompletedEvent {
  type: "message.completed";
  message: {
    id: string;
    role: "assistant";
    content: string;
    usage: {
      promptTokens: number;
      completionTokens: number;
      totalTokens: number;
      model: string;
    };
    toolCalls?: ToolCall[];
  };
}

/**
 * Tool execution event
 */
export interface ToolExecuteEvent {
  type: "tool.execute.before" | "tool.execute.after";
  tool: string;
  args: Record<string, unknown>;
  result?: unknown;
  duration?: number;
  sessionID: string;
  callID: string;
}

/**
 * Session created event
 */
export interface SessionCreatedEvent {
  type: "session.created";
  session: {
    id: string;
    model: string;
    timestamp: Date;
  };
}

/**
 * Config changed event
 */
export interface ConfigChangedEvent {
  type: "config.changed";
  config: Record<string, unknown>;
}

/**
 * Tool call structure
 */
export interface ToolCall {
  name: string;
  args: Record<string, unknown>;
  result?: unknown;
}

/**
 * Chat message input
 */
export interface ChatMessageInput {
  sessionID: string;
  messageID: string;
  agent: string;
  model: string;
}

/**
 * Chat message output
 */
export interface ChatMessageOutput {
  message: string;
  parts: Array<{ type: string; content: string }>;
}

/**
 * Tool execution input
 */
export interface ToolExecutionInput {
  tool: string;
  sessionID: string;
  callID: string;
}

/**
 * Tool execution output
 */
export interface ToolExecutionOutput {
  title: string;
  output: unknown;
  metadata: Record<string, unknown>;
}

/**
 * OpenCode config
 */
export interface OpenCodeConfig {
  [key: string]: unknown;
}
