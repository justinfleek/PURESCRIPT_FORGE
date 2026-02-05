// OpenAI-Compatible Chunk Conversion FFI
export function fromOaCompatibleChunkImpl(chunkStr) {
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

    return {
      id: json.id ?? "",
      object: "chat.completion.chunk",
      created: json.created ?? Math.floor(Date.now() / 1000),
      model: json.model ?? "",
      choices: json.choices ?? [],
      usage: json.usage,
    };
  } catch (e) {
    return { error: chunkStr };
  }
}

export function toOaCompatibleChunkImpl(chunk) {
  try {
    if (!chunk.choices || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    return `data: ${JSON.stringify(chunk)}`;
  } catch (e) {
    return "";
  }
}
