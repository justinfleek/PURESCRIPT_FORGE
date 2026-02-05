// OpenAI-Compatible Response Conversion FFI
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling
export function fromOaCompatibleResponseImpl(respJson) {
  try {
    const resp = typeof respJson === "string" ? JSON.parse(respJson) : respJson;
    if (typeof resp !== "object" || resp === null || !Array.isArray(resp.choices)) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const choice = resp.choices[0];
    if (typeof choice !== "object" || choice === null) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const message = choice.message;
    if (typeof message !== "object" || message === null) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const respId = resp.id;
    const idValue = typeof respId === "string" && respId.length > 0 ? respId : "";

    const respCreated = resp.created;
    const createdValue = typeof respCreated === "number" ? respCreated : Math.floor(Date.now() / 1000);

    const respModel = resp.model;
    const modelValue = typeof respModel === "string" && respModel.length > 0 ? respModel : "";

    return {
      id: idValue,
      object: "chat.completion",
      created: createdValue,
      model: modelValue,
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
    if (typeof resp !== "object" || resp === null || !Array.isArray(resp.choices) || resp.choices.length === 0) {
      return JSON.stringify({ id: "", model: "", choices: [] });
    }

    const choice = resp.choices[0];
    const msg = choice.message;
    if (typeof msg !== "object" || msg === null) {
      return JSON.stringify({ id: "", model: "", choices: [] });
    }

    const respId = resp.id;
    const idValue = typeof respId === "string" && respId.length > 0 ? respId : "";

    const respCreated = resp.created;
    const createdValue = typeof respCreated === "number" ? respCreated : Math.floor(Date.now() / 1000);

    const respModel = resp.model;
    const modelValue = typeof respModel === "string" && respModel.length > 0 ? respModel : "";

    return JSON.stringify({
      id: idValue,
      object: "chat.completion",
      created: createdValue,
      model: modelValue,
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
