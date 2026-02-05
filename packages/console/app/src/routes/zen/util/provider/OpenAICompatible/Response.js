// OpenAI-Compatible Response Conversion FFI
export function fromOaCompatibleResponseImpl(respJson) {
  try {
    const resp = typeof respJson === "string" ? JSON.parse(respJson) : respJson;
    if (!resp || typeof resp !== "object" || !Array.isArray(resp.choices)) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const choice = resp.choices[0];
    if (!choice) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const message = choice.message;
    if (!message) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    return {
      id: resp.id ?? "",
      object: "chat.completion",
      created: resp.created ?? Math.floor(Date.now() / 1000),
      model: resp.model ?? "",
      choices: [
        {
          index: 0,
          message: {
            role: "assistant",
            content: message.content,
            tool_calls: message.tool_calls,
          },
          finish_reason: choice.finish_reason,
        },
      ],
      usage: resp.usage,
    };
  } catch (e) {
    return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
  }
}

export function toOaCompatibleResponseImpl(resp) {
  try {
    if (!resp || typeof resp !== "object" || !Array.isArray(resp.choices) || resp.choices.length === 0) {
      return JSON.stringify({ id: "", model: "", choices: [] });
    }

    const choice = resp.choices[0];
    const msg = choice.message;
    if (!msg) {
      return JSON.stringify({ id: "", model: "", choices: [] });
    }

    return JSON.stringify({
      id: resp.id ?? "",
      object: "chat.completion",
      created: resp.created ?? Math.floor(Date.now() / 1000),
      model: resp.model ?? "",
      choices: [
        {
          index: 0,
          message: {
            role: "assistant",
            content: msg.content,
            tool_calls: msg.tool_calls,
          },
          finish_reason: choice.finish_reason,
        },
      ],
      usage: resp.usage,
    });
  } catch (e) {
    return JSON.stringify({ id: "", model: "", choices: [] });
  }
}
