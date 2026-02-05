// Anthropic Chunk Conversion FFI
export function fromAnthropicChunkImpl(chunkStr) {
  try {
    const lines = chunkStr.split("\n");
    const ev = lines[0];
    const dl = lines[1];
    if (!ev || !dl || !dl.startsWith("data: ")) {
      return { error: chunkStr };
    }

    let json;
    try {
      json = JSON.parse(dl.slice(6));
    } catch (e) {
      return { error: chunkStr };
    }

    const e = ev.replace("event: ", "").trim();
    const out = {
      id: json.message?.id ?? json.id ?? "",
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: json.message?.model ?? json.model ?? "",
      choices: [],
    };

    if (e === "message_start") {
      // Initialize
    } else if (e === "content_block_delta" && json.delta?.type === "text_delta") {
      out.choices.push({ index: 0, delta: { content: json.delta.text }, finish_reason: null });
    } else if (e === "content_block_start" && json.content_block?.type === "tool_use") {
      const cb = json.content_block;
      out.choices.push({
        index: 0,
        delta: {
          tool_calls: [{ index: 0, id: cb.id, type: "function", function: { name: cb.name, arguments: "" } }],
        },
        finish_reason: null,
      });
    } else if (e === "content_block_delta" && json.delta?.type === "input_json_delta") {
      out.choices.push({
        index: 0,
        delta: { tool_calls: [{ index: 0, function: { arguments: json.delta.partial_json } }] },
        finish_reason: null,
      });
    } else if (e === "message_delta" && json.delta?.stop_reason) {
      const finish = (r) => {
        if (r === "end_turn") return "stop";
        if (r === "tool_use") return "tool_calls";
        if (r === "max_tokens") return "length";
        if (r === "content_filtered") return "content_filter";
        return null;
      };
      out.choices.push({ index: 0, delta: {}, finish_reason: finish(json.delta.stop_reason) });

      const u = json.usage;
      if (u) {
        out.usage = {
          prompt_tokens: u.input_tokens,
          completion_tokens: u.output_tokens,
          total_tokens: (u.input_tokens || 0) + (u.output_tokens || 0),
        };
      }
    }

    return out;
  } catch (e) {
    return { error: chunkStr };
  }
}

export function toAnthropicChunkImpl(chunk) {
  try {
    if (!chunk.choices || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    const choice = chunk.choices[0];
    const d = choice.delta;
    if (!d) return "";

    if (d.content) {
      return `event: content_block_delta\ndata: ${JSON.stringify({ type: "content_block_delta", delta: { type: "text_delta", text: d.content }, index: 0 })}`;
    }

    if (d.tool_calls) {
      for (const tc of d.tool_calls) {
        if (tc.function?.name) {
          return `event: content_block_start\ndata: ${JSON.stringify({ type: "content_block_start", content_block: { type: "tool_use", id: tc.id, name: tc.function.name, input: {} }, index: 0 })}`;
        }
        if (tc.function?.arguments) {
          return `event: content_block_delta\ndata: ${JSON.stringify({ type: "content_block_delta", delta: { type: "input_json_delta", partial_json: tc.function.arguments }, index: 0 })}`;
        }
      }
    }

    if (choice.finish_reason) {
      const stopReason = (() => {
        const r = choice.finish_reason;
        if (r === "stop") return "end_turn";
        if (r === "tool_calls") return "tool_use";
        if (r === "length") return "max_tokens";
        if (r === "content_filter") return "content_filtered";
        return null;
      })();

      const u = chunk.usage;
      const usage = u
        ? {
            input_tokens: u.prompt_tokens,
            output_tokens: u.completion_tokens,
          }
        : undefined;

      return `event: message_delta\ndata: ${JSON.stringify({ type: "message_delta", delta: { stop_reason: stopReason }, usage })}`;
    }

    return "";
  } catch (e) {
    return "";
  }
}
