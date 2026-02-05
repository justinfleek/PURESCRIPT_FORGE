// Anthropic Response Conversion FFI
export function fromAnthropicResponseImpl(respJson) {
  try {
    const resp = typeof respJson === "string" ? JSON.parse(respJson) : respJson;
    if (!resp || typeof resp !== "object") {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const id = resp.id ?? `msg_${Math.random().toString(36).slice(2)}`;
    const model = resp.model ?? "";

    const content = Array.isArray(resp.content) ? resp.content : [];
    const texts = content.filter((c) => c.type === "text").map((c) => c.text);
    const text = texts.join("");

    const tcs = content
      .filter((c) => c.type === "tool_use")
      .map((c) => {
        const input = typeof c.input === "string" ? c.input : JSON.stringify(c.input ?? {});
        return {
          id: c.id,
          type: "function",
          function: { name: c.name, arguments: input },
        };
      });

    const finish = (r) => {
      if (r === "end_turn") return "stop";
      if (r === "tool_use") return "tool_calls";
      if (r === "max_tokens") return "length";
      if (r === "content_filtered") return "content_filter";
      return null;
    };

    const u = resp.usage;
    const usage = u
      ? {
          prompt_tokens: u.input_tokens,
          completion_tokens: u.output_tokens,
          total_tokens: (u.input_tokens || 0) + (u.output_tokens || 0),
        }
      : undefined;

    return {
      id,
      object: "chat.completion",
      created: Math.floor(Date.now() / 1000),
      model,
      choices: [
        {
          index: 0,
          message: {
            role: "assistant",
            ...(text && text.length > 0 ? { content: text } : {}),
            ...(tcs.length > 0 ? { tool_calls: tcs } : {}),
          },
          finish_reason: finish(resp.stop_reason ?? null),
        },
      ],
      ...(usage ? { usage } : {}),
    };
  } catch (e) {
    return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
  }
}

export function toAnthropicResponseImpl(resp) {
  try {
    if (!resp || typeof resp !== "object" || !Array.isArray(resp.choices) || resp.choices.length === 0) {
      return JSON.stringify({ id: "", model: "", content: [] });
    }

    const choice = resp.choices[0];
    const msg = choice.message;
    if (!msg) {
      return JSON.stringify({ id: "", model: "", content: [] });
    }

    const content = [];
    if (typeof msg.content === "string" && msg.content.length > 0) {
      content.push({ type: "text", text: msg.content });
    }
    if (Array.isArray(msg.tool_calls)) {
      for (const tc of msg.tool_calls) {
        if (tc.type === "function" && tc.function) {
          let input;
          try {
            input = JSON.parse(tc.function.arguments);
          } catch {
            input = tc.function.arguments;
          }
          content.push({
            type: "tool_use",
            id: tc.id,
            name: tc.function.name,
            input,
          });
        }
      }
    }

    const stopReason = (() => {
      const r = choice.finish_reason;
      if (r === "stop") return "end_turn";
      if (r === "tool_calls") return "tool_use";
      if (r === "length") return "max_tokens";
      if (r === "content_filter") return "content_filtered";
      return null;
    })();

    const u = resp.usage;
    const usage = u
      ? {
          input_tokens: u.prompt_tokens,
          output_tokens: u.completion_tokens,
        }
      : undefined;

    return JSON.stringify({
      id: resp.id ?? `msg_${Math.random().toString(36).slice(2)}`,
      model: resp.model,
      content,
      stop_reason: stopReason,
      usage,
    });
  } catch (e) {
    return JSON.stringify({ id: "", model: "", content: [] });
  }
}
