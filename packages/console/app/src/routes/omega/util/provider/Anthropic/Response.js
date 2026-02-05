// Anthropic Response Conversion FFI
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling
export function fromAnthropicResponseImpl(respJson) {
  try {
    const resp = typeof respJson === "string" ? JSON.parse(respJson) : respJson;
    if (typeof resp !== "object" || resp === null) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const respId = resp.id;
    const id = typeof respId === "string" && respId.length > 0 ? respId : `msg_${Math.random().toString(36).slice(2)}`;
    const respModel = resp.model;
    const model = typeof respModel === "string" && respModel.length > 0 ? respModel : "";

    const content = Array.isArray(resp.content) ? resp.content : [];
    const texts = content.filter((c) => typeof c === "object" && c !== null && typeof c.type === "string" && c.type === "text" && typeof c.text === "string").map((c) => c.text);
    const text = texts.join("");

    const tcs = content
      .filter((c) => typeof c === "object" && c !== null && typeof c.type === "string" && c.type === "tool_use")
      .map((c) => {
        const cInput = c.input;
        const input = typeof cInput === "string" ? cInput : (typeof cInput === "object" && cInput !== null ? JSON.stringify(cInput) : JSON.stringify({}));
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
    let usageResult = null;
    if (typeof u === "object" && u !== null) {
      const uInputTokens = u.input_tokens;
      const uOutputTokens = u.output_tokens;
      const inputTokensValue = typeof uInputTokens === "number" ? uInputTokens : 0;
      const outputTokensValue = typeof uOutputTokens === "number" ? uOutputTokens : 0;
      const totalTokensValue = inputTokensValue + outputTokensValue;
      usageResult = {
        prompt_tokens: inputTokensValue,
        completion_tokens: outputTokensValue,
        total_tokens: totalTokensValue,
      };
    }

    const result = {
      id,
      object: "chat.completion",
      created: Math.floor(Date.now() / 1000),
      model,
      choices: [
        {
          index: 0,
          message: {
            role: "assistant",
          },
          finish_reason: finish(resp.stop_reason),
        },
      ],
    };
    if (typeof text === "string" && text.length > 0) {
      result.choices[0].message.content = text;
    }
    if (Array.isArray(tcs) && tcs.length > 0) {
      result.choices[0].message.tool_calls = tcs;
    }
    if (usageResult !== null) {
      result.usage = usageResult;
    }
    return result;
  } catch (e) {
    return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
  }
}

export function toAnthropicResponseImpl(resp) {
  try {
    if (typeof resp !== "object" || resp === null || !Array.isArray(resp.choices) || resp.choices.length === 0) {
      return JSON.stringify({ id: "", model: "", content: [] });
    }

    const choice = resp.choices[0];
    const msg = choice.message;
    if (typeof msg !== "object" || msg === null) {
      return JSON.stringify({ id: "", model: "", content: [] });
    }

    const content = [];
    if (typeof msg.content === "string" && msg.content.length > 0) {
      content.push({ type: "text", text: msg.content });
    }
    if (Array.isArray(msg.tool_calls)) {
      for (const tc of msg.tool_calls) {
        if (typeof tc === "object" && tc !== null && typeof tc.type === "string" && tc.type === "function") {
          const tcFunction = tc.function;
          if (typeof tcFunction === "object" && tcFunction !== null) {
            let input;
            try {
              input = JSON.parse(tcFunction.arguments);
            } catch {
              input = tcFunction.arguments;
            }
            content.push({
              type: "tool_use",
              id: tc.id,
              name: tcFunction.name,
              input,
            });
          }
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
    let usageResult = null;
    if (typeof u === "object" && u !== null) {
      usageResult = {
        input_tokens: typeof u.prompt_tokens === "number" ? u.prompt_tokens : 0,
        output_tokens: typeof u.completion_tokens === "number" ? u.completion_tokens : 0,
      };
    }

    const respId = resp.id;
    const idValue = typeof respId === "string" && respId.length > 0 ? respId : `msg_${Math.random().toString(36).slice(2)}`;
    const result = {
      id: idValue,
      model: resp.model,
      content,
      stop_reason: stopReason,
    };
    if (usageResult !== null) {
      result.usage = usageResult;
    }
    return JSON.stringify(result);
  } catch (e) {
    return JSON.stringify({ id: "", model: "", content: [] });
  }
}
