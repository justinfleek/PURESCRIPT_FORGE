// OpenAI-Compatible Chunk Conversion FFI
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling
export function fromOaCompatibleChunkImpl(chunkStr) {
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

    const jsonId = json.id;
    const idValue = typeof jsonId === "string" && jsonId.length > 0 ? jsonId : "";

    const jsonCreated = json.created;
    const createdValue = typeof jsonCreated === "number" ? jsonCreated : Math.floor(Date.now() / 1000);

    const jsonModel = json.model;
    const modelValue = typeof jsonModel === "string" && jsonModel.length > 0 ? jsonModel : "";

    const jsonChoices = json.choices;
    const choicesValue = Array.isArray(jsonChoices) ? jsonChoices : [];

    return {
      id: idValue,
      object: "chat.completion.chunk",
      created: createdValue,
      model: modelValue,
      choices: choicesValue,
      usage: json.usage,
    };
  } catch (e) {
    return { error: chunkStr };
  }
}

export function toOaCompatibleChunkImpl(chunk) {
  try {
    if (typeof chunk !== "object" || chunk === null || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    return `data: ${JSON.stringify(chunk)}`;
  } catch (e) {
    return "";
  }
}
