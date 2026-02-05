// Google Chunk Conversion FFI
export function fromGoogleChunkImpl(chunkStr) {
  try {
    if (!chunkStr.startsWith("data: ")) {
      return { error: chunkStr };
    }

    let json;
    try {
      json = JSON.parse(chunkStr.slice(6));
    } catch (e) {
      return { error: chunkStr };
    }

    const candidates = Array.isArray(json.candidates) ? json.candidates : [];
    const candidate = candidates[0];
    const parts = Array.isArray(candidate?.content?.parts) ? candidate.content.parts : [];
    const text = parts.filter((p) => p.text).map((p) => p.text).join("");

    const finishReason = (() => {
      const r = candidate?.finishReason;
      if (r === "STOP") return "stop";
      if (r === "MAX_TOKENS") return "length";
      if (r === "SAFETY") return "content_filter";
      return null;
    })();

    return {
      id: `chatcmpl_${Math.random().toString(36).slice(2)}`,
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: json.model ?? "",
      choices: [
        {
          index: 0,
          delta: text ? { content: text } : {},
          finish_reason: finishReason,
        },
      ],
      usage: json.usageMetadata,
    };
  } catch (e) {
    return { error: chunkStr };
  }
}

export function toGoogleChunkImpl(chunk) {
  try {
    if (!chunk.choices || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    const choice = chunk.choices[0];
    const d = choice.delta;
    if (!d) return "";

    const finishReason = (() => {
      const r = choice.finish_reason;
      if (r === "stop") return "STOP";
      if (r === "length") return "MAX_TOKENS";
      if (r === "content_filter") return "SAFETY";
      return null;
    })();

    return `data: ${JSON.stringify({
      candidates: [
        {
          content: {
            parts: d.content ? [{ text: d.content }] : [],
          },
          finishReason,
        },
      ],
      usageMetadata: chunk.usage,
    })}`;
  } catch (e) {
    return "";
  }
}
