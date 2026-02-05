// Anthropic Chunk Conversion FFI
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling
export function fromAnthropicChunkImpl(chunkStr) {
  try {
    const lines = chunkStr.split("\n");
    const ev = lines[0];
    const dl = lines[1];
    if (typeof ev !== "string" || typeof dl !== "string" || dl.length < 6 || dl.substring(0, 6) !== "data: ") {
      return { error: chunkStr };
    }

    let json;
    try {
      json = JSON.parse(dl.slice(6));
    } catch (e) {
      return { error: chunkStr };
    }

    const e = ev.replace("event: ", "").trim();
    const jsonMessage = json.message;
    const jsonId = json.id;
    const jsonMessageId = typeof jsonMessage === "object" && jsonMessage !== null ? jsonMessage.id : null;
    const idValue = typeof jsonMessageId === "string" && jsonMessageId.length > 0 ? jsonMessageId : (typeof jsonId === "string" && jsonId.length > 0 ? jsonId : "");

    const jsonMessageModel = typeof jsonMessage === "object" && jsonMessage !== null ? jsonMessage.model : null;
    const jsonModel = json.model;
    const modelValue = typeof jsonMessageModel === "string" && jsonMessageModel.length > 0 ? jsonMessageModel : (typeof jsonModel === "string" && jsonModel.length > 0 ? jsonModel : "");

    const out = {
      id: idValue,
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: modelValue,
      choices: [],
    };

    if (e === "message_start") {
      // Initialize
    } else if (e === "content_block_delta") {
      const jsonDelta = json.delta;
      if (typeof jsonDelta === "object" && jsonDelta !== null && typeof jsonDelta.type === "string" && jsonDelta.type === "text_delta") {
        out.choices.push({ index: 0, delta: { content: jsonDelta.text }, finish_reason: null });
      }
    } else if (e === "content_block_start") {
      const jsonContentBlock = json.content_block;
      if (typeof jsonContentBlock === "object" && jsonContentBlock !== null && typeof jsonContentBlock.type === "string" && jsonContentBlock.type === "tool_use") {
        const cb = jsonContentBlock;
        out.choices.push({
          index: 0,
          delta: {
            tool_calls: [{ index: 0, id: cb.id, type: "function", function: { name: cb.name, arguments: "" } }],
          },
          finish_reason: null,
        });
      }
    } else if (e === "content_block_delta") {
      const jsonDelta = json.delta;
      if (typeof jsonDelta === "object" && jsonDelta !== null && typeof jsonDelta.type === "string" && jsonDelta.type === "input_json_delta") {
        out.choices.push({
          index: 0,
          delta: { tool_calls: [{ index: 0, function: { arguments: jsonDelta.partial_json } }] },
          finish_reason: null,
        });
      }
    } else if (e === "message_delta") {
      const jsonDelta = json.delta;
      if (typeof jsonDelta === "object" && jsonDelta !== null && typeof jsonDelta.stop_reason === "string" && jsonDelta.stop_reason.length > 0) {
        const finish = (r) => {
          if (r === "end_turn") return "stop";
          if (r === "tool_use") return "tool_calls";
          if (r === "max_tokens") return "length";
          if (r === "content_filtered") return "content_filter";
          return null;
        };
        out.choices.push({ index: 0, delta: {}, finish_reason: finish(jsonDelta.stop_reason) });

        const u = json.usage;
        if (typeof u === "object" && u !== null) {
          const inputTokensValue = typeof u.input_tokens === "number" ? u.input_tokens : 0;
          const outputTokensValue = typeof u.output_tokens === "number" ? u.output_tokens : 0;
          const totalTokensValue = inputTokensValue + outputTokensValue;
          out.usage = {
            prompt_tokens: inputTokensValue,
            completion_tokens: outputTokensValue,
            total_tokens: totalTokensValue,
          };
        }
      }
    }

    return out;
  } catch (e) {
    return { error: chunkStr };
  }
}

export function toAnthropicChunkImpl(chunk) {
  try {
    if (typeof chunk !== "object" || chunk === null || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    const choice = chunk.choices[0];
    const d = choice.delta;
    if (typeof d !== "object" || d === null) return "";

    if (typeof d.content === "string" && d.content.length > 0) {
      return `event: content_block_delta\ndata: ${JSON.stringify({ type: "content_block_delta", delta: { type: "text_delta", text: d.content }, index: 0 })}`;
    }

    if (Array.isArray(d.tool_calls)) {
      for (const tc of d.tool_calls) {
        if (typeof tc === "object" && tc !== null) {
          const tcFunction = tc.function;
          if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.name === "string" && tcFunction.name.length > 0) {
            return `event: content_block_start\ndata: ${JSON.stringify({ type: "content_block_start", content_block: { type: "tool_use", id: tc.id, name: tcFunction.name, input: {} }, index: 0 })}`;
          }
          if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.arguments === "string" && tcFunction.arguments.length > 0) {
            return `event: content_block_delta\ndata: ${JSON.stringify({ type: "content_block_delta", delta: { type: "input_json_delta", partial_json: tcFunction.arguments }, index: 0 })}`;
          }
        }
      }
    }

    if (typeof choice.finish_reason === "string" && choice.finish_reason.length > 0) {
      const stopReason = (() => {
        const r = choice.finish_reason;
        if (r === "stop") return "end_turn";
        if (r === "tool_calls") return "tool_use";
        if (r === "length") return "max_tokens";
        if (r === "content_filter") return "content_filtered";
        return null;
      })();

      const u = chunk.usage;
      let usageResult = null;
      if (typeof u === "object" && u !== null) {
        usageResult = {
          input_tokens: typeof u.prompt_tokens === "number" ? u.prompt_tokens : 0,
          output_tokens: typeof u.completion_tokens === "number" ? u.completion_tokens : 0,
        };
      }

      const result = {
        type: "message_delta",
        delta: { stop_reason: stopReason },
      };
      if (usageResult !== null) {
        result.usage = usageResult;
      }
      return `event: message_delta\ndata: ${JSON.stringify(result)}`;
    }

    return "";
  } catch (e) {
    return "";
  }
}
