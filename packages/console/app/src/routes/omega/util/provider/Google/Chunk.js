// Google Chunk Conversion FFI
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling
export function fromGoogleChunkImpl(chunkStr) {
  try {
    if (typeof chunkStr !== "string" || chunkStr.length < 6 || chunkStr.substring(0, 6) !== "data: ") {
      return { error: chunkStr };
    }

    let json;
    try {
      json = JSON.parse(chunkStr.slice(6));
    } catch (e) {
      return { error: chunkStr };
    }

    const candidates = Array.isArray(json.candidates) ? json.candidates : [];
    const candidate = candidates.length > 0 ? candidates[0] : null;
    const candidateContent = typeof candidate === "object" && candidate !== null ? candidate.content : null;
    const candidateContentParts = typeof candidateContent === "object" && candidateContent !== null && Array.isArray(candidateContent.parts) ? candidateContent.parts : [];
    const parts = candidateContentParts;
    const text = parts.filter((p) => typeof p === "object" && p !== null && typeof p.text === "string").map((p) => p.text).join("");

    const finishReason = (() => {
      const candidateFinishReason = typeof candidate === "object" && candidate !== null ? candidate.finishReason : null;
      const r = typeof candidateFinishReason === "string" && candidateFinishReason.length > 0 ? candidateFinishReason : "";
      if (r === "STOP") return "stop";
      if (r === "MAX_TOKENS") return "length";
      if (r === "SAFETY") return "content_filter";
      return null;
    })();

    const jsonModel = json.model;
    const modelValue = typeof jsonModel === "string" && jsonModel.length > 0 ? jsonModel : "";

    return {
      id: `chatcmpl_${Math.random().toString(36).slice(2)}`,
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: modelValue,
      choices: [
        {
          index: 0,
          delta: typeof text === "string" && text.length > 0 ? { content: text } : {},
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
    if (typeof chunk !== "object" || chunk === null || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    const choice = chunk.choices[0];
    const d = choice.delta;
    if (typeof d !== "object" || d === null) return "";

    const finishReason = (() => {
      const r = choice.finish_reason;
      if (r === "stop") return "STOP";
      if (r === "length") return "MAX_TOKENS";
      if (r === "content_filter") return "SAFETY";
      return null;
    })();

    const dContent = d.content;
    const partsValue = typeof dContent === "string" && dContent.length > 0 ? [{ text: dContent }] : [];

    return `data: ${JSON.stringify({
      candidates: [
        {
          content: {
            parts: partsValue,
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
