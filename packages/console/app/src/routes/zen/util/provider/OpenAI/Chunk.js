// OpenAI Chunk Conversion FFI
// Full implementation of fromOpenaiChunk and toOpenaiChunk
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-04

// Full fromOpenaiChunk implementation
export function fromOpenaiChunkImpl(chunkStr) {
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

    const respObj = json.response ?? {};

    const out = {
      id: respObj.id ?? json.id ?? "",
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: respObj.model ?? json.model ?? "",
      choices: [],
    };

    const e = ev.replace("event: ", "").trim();

    if (e === "response.output_text.delta") {
      const d = json.delta ?? json.text ?? json.output_text_delta;
      if (typeof d === "string" && d.length > 0) {
        out.choices.push({ index: 0, delta: { content: d }, finish_reason: null });
      }
    }

    if (e === "response.output_item.added" && json.item?.type === "function_call") {
      const name = json.item?.name;
      const id = json.item?.id;
      if (typeof name === "string" && name.length > 0) {
        out.choices.push({
          index: 0,
          delta: {
            tool_calls: [{ index: 0, id, type: "function", function: { name, arguments: "" } }],
          },
          finish_reason: null,
        });
      }
    }

    if (e === "response.function_call_arguments.delta") {
      const a = json.delta ?? json.arguments_delta;
      if (typeof a === "string" && a.length > 0) {
        out.choices.push({
          index: 0,
          delta: { tool_calls: [{ index: 0, function: { arguments: a } }] },
          finish_reason: null,
        });
      }
    }

    if (e === "response.completed") {
      const fr = (() => {
        const sr = respObj.stop_reason ?? json.stop_reason;
        if (sr === "stop") return "stop";
        if (sr === "tool_call" || sr === "tool_calls") return "tool_calls";
        if (sr === "length" || sr === "max_output_tokens") return "length";
        if (sr === "content_filter") return "content_filter";
        return null;
      })();
      out.choices.push({ index: 0, delta: {}, finish_reason: fr });

      const u = respObj.usage ?? json.response?.usage;
      if (u) {
        out.usage = {
          prompt_tokens: u.input_tokens,
          completion_tokens: u.output_tokens,
          total_tokens: (u.input_tokens || 0) + (u.output_tokens || 0),
          ...(u.input_tokens_details?.cached_tokens
            ? { prompt_tokens_details: { cached_tokens: u.input_tokens_details.cached_tokens } }
            : {}),
        };
      }
    }

    return out;
  } catch (e) {
    return { error: chunkStr };
  }
}

// Full toOpenaiChunk implementation
export function toOpenaiChunkImpl(chunk) {
  try {
    if (!chunk.choices || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    const choice = chunk.choices[0];
    const d = choice.delta;
    if (!d) return "";

    const id = chunk.id;
    const model = chunk.model;

    if (d.content) {
      const data = {
        id,
        type: "response.output_text.delta",
        delta: d.content,
        response: { id, model },
      };
      return `event: response.output_text.delta\ndata: ${JSON.stringify(data)}`;
    }

    if (d.tool_calls) {
      for (const tc of d.tool_calls) {
        if (tc.function?.name) {
          const data = {
            type: "response.output_item.added",
            output_index: 0,
            item: {
              id: tc.id,
              type: "function_call",
              name: tc.function.name,
              call_id: tc.id,
              arguments: "",
            },
          };
          return `event: response.output_item.added\ndata: ${JSON.stringify(data)}`;
        }
        if (tc.function?.arguments) {
          const data = {
            type: "response.function_call_arguments.delta",
            output_index: 0,
            delta: tc.function.arguments,
          };
          return `event: response.function_call_arguments.delta\ndata: ${JSON.stringify(data)}`;
        }
      }
    }

    if (choice.finish_reason) {
      const u = chunk.usage;
      const usage = u
        ? {
            input_tokens: u.prompt_tokens,
            output_tokens: u.completion_tokens,
            total_tokens: u.total_tokens,
            ...(u.prompt_tokens_details?.cached_tokens
              ? { input_tokens_details: { cached_tokens: u.prompt_tokens_details.cached_tokens } }
              : {}),
          }
        : undefined;

      const data = {
        id,
        type: "response.completed",
        response: { id, model, ...(usage ? { usage } : {}) },
      };
      return `event: response.completed\ndata: ${JSON.stringify(data)}`;
    }

    return "";
  } catch (e) {
    return "";
  }
}
