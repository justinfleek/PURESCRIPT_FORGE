// FFI for Forge.Tool.Batch
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/batch.ts

import { Session } from "../session/Index.js";
import { Identifier } from "../id/Index.js";
import { ToolRegistry } from "./Registry.js";

const DISALLOWED = new Set(["batch"]);
const FILTERED_FROM_SUGGESTIONS = new Set(["invalid", "patch", ...DISALLOWED]);

export const execute = (params) => (ctx) => async () => {
  const toolCalls = params.tool_calls.slice(0, 25);
  const discardedCalls = params.tool_calls.slice(25);

  const availableTools = await ToolRegistry.tools({ modelID: "", providerID: "" });
  const toolMap = new Map(availableTools.map((t) => [t.id, t]));

  const executeCall = async (call) => {
    const callStartTime = Date.now();
    const partID = Identifier.ascending("part");

    try {
      if (DISALLOWED.has(call.tool)) {
        throw new Error(
          `Tool '${call.tool}' is not allowed in batch. Disallowed tools: ${Array.from(DISALLOWED).join(", ")}`
        );
      }

      const tool = toolMap.get(call.tool);
      if (!tool) {
        const availableToolsList = Array.from(toolMap.keys()).filter((name) => !FILTERED_FROM_SUGGESTIONS.has(name));
        throw new Error(
          `Tool '${call.tool}' not in registry. External tools (MCP, environment) cannot be batched - call them directly. Available tools: ${availableToolsList.join(", ")}`
        );
      }
      const validatedParams = tool.parameters.parse(call.parameters);

      await Session.updatePart({
        id: partID,
        messageID: ctx.messageID,
        sessionID: ctx.sessionID,
        type: "tool",
        tool: call.tool,
        callID: partID,
        state: {
          status: "running",
          input: call.parameters,
          time: {
            start: callStartTime,
          },
        },
      });

      const result = await tool.execute(validatedParams, { ...ctx, callID: partID });

      await Session.updatePart({
        id: partID,
        messageID: ctx.messageID,
        sessionID: ctx.sessionID,
        type: "tool",
        tool: call.tool,
        callID: partID,
        state: {
          status: "completed",
          input: call.parameters,
          output: result.output,
          title: result.title,
          metadata: result.metadata,
          attachments: result.attachments,
          time: {
            start: callStartTime,
            end: Date.now(),
          },
        },
      });

      return { success: true, tool: call.tool, result };
    } catch (error) {
      await Session.updatePart({
        id: partID,
        messageID: ctx.messageID,
        sessionID: ctx.sessionID,
        type: "tool",
        tool: call.tool,
        callID: partID,
        state: {
          status: "error",
          input: call.parameters,
          error: error instanceof Error ? error.message : String(error),
          time: {
            start: callStartTime,
            end: Date.now(),
          },
        },
      });

      return { success: false, tool: call.tool, error };
    }
  };

  const results = await Promise.all(toolCalls.map((call) => executeCall(call)));

  // Add discarded calls as errors
  const now = Date.now();
  for (const call of discardedCalls) {
    const partID = Identifier.ascending("part");
    await Session.updatePart({
      id: partID,
      messageID: ctx.messageID,
      sessionID: ctx.sessionID,
      type: "tool",
      tool: call.tool,
      callID: partID,
      state: {
        status: "error",
        input: call.parameters,
        error: "Maximum of 25 tools allowed in batch",
        time: { start: now, end: now },
      },
    });
    results.push({
      success: false,
      tool: call.tool,
      error: new Error("Maximum of 25 tools allowed in batch"),
    });
  }

  const successfulCalls = results.filter((r) => r.success).length;
  const failedCalls = results.length - successfulCalls;

  const outputMessage =
    failedCalls > 0
      ? `Executed ${successfulCalls}/${results.length} tools successfully. ${failedCalls} failed.`
      : `All ${successfulCalls} tools executed successfully.\n\nKeep using the batch tool for optimal performance in your next response!`;

  return {
    title: `Batch execution (${successfulCalls}/${results.length} successful)`,
    output: outputMessage,
    attachments: results.filter((result) => result.success).flatMap((r) => r.result.attachments ?? []),
    metadata: {
      totalCalls: results.length,
      successful: successfulCalls,
      failed: failedCalls,
      tools: params.tool_calls.map((c) => c.tool),
      details: results.map((r) => ({ tool: r.tool, success: r.success })),
    },
  };
};
