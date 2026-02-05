// Google Response Conversion FFI
export function fromGoogleResponseImpl(respJson) {
  try {
    const resp = typeof respJson === "string" ? JSON.parse(respJson) : respJson;
    if (!resp || typeof resp !== "object") {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const candidates = Array.isArray(resp.candidates) ? resp.candidates : [];
    const candidate = candidates[0];
    if (!candidate) {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const parts = Array.isArray(candidate.content?.parts) ? candidate.content.parts : [];
    const text = parts.filter((p) => p.text).map((p) => p.text).join("");

    const finishReason = (() => {
      const r = candidate.finishReason;
      if (r === "STOP") return "stop";
      if (r === "MAX_TOKENS") return "length";
      if (r === "SAFETY") return "content_filter";
      return null;
    })();

    const u = resp.usageMetadata;
    const usage = u
      ? {
          prompt_tokens: u.promptTokenCount,
          completion_tokens: u.candidatesTokenCount,
          total_tokens: u.totalTokenCount,
        }
      : undefined;

    return {
      id: `chatcmpl_${Math.random().toString(36).slice(2)}`,
      object: "chat.completion",
      created: Math.floor(Date.now() / 1000),
      model: resp.model ?? "",
      choices: [
        {
          index: 0,
          message: {
            role: "assistant",
            content: text,
          },
          finish_reason: finishReason,
        },
      ],
      usage,
    };
  } catch (e) {
    return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
  }
}

export function toGoogleResponseImpl(resp) {
  try {
    if (!resp || typeof resp !== "object" || !Array.isArray(resp.choices) || resp.choices.length === 0) {
      return JSON.stringify({ candidates: [] });
    }

    const choice = resp.choices[0];
    const msg = choice.message;
    if (!msg) {
      return JSON.stringify({ candidates: [] });
    }

    const finishReason = (() => {
      const r = choice.finish_reason;
      if (r === "stop") return "STOP";
      if (r === "length") return "MAX_TOKENS";
      if (r === "content_filter") return "SAFETY";
      return null;
    })();

    const u = resp.usage;
    const usageMetadata = u
      ? {
          promptTokenCount: u.prompt_tokens,
          candidatesTokenCount: u.completion_tokens,
          totalTokenCount: u.total_tokens,
        }
      : undefined;

    return JSON.stringify({
      candidates: [
        {
          content: {
            parts: typeof msg.content === "string" ? [{ text: msg.content }] : [],
          },
          finishReason,
        },
      ],
      usageMetadata,
    });
  } catch (e) {
    return JSON.stringify({ candidates: [] });
  }
}
