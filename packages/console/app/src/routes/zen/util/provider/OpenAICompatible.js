// OpenAI-Compatible Provider FFI
// JavaScript implementations for OpenAI-compatible provider functions

let usageStore = null;

export function modifyHeadersImpl(bodyJson, apiKey) {
  const headers = globalThis._currentHeadersObj;
  if (!headers || !(headers instanceof Headers)) {
    return;
  }
  headers.set("authorization", `Bearer ${apiKey}`);
}

export function modifyBodyImpl(bodyJson) {
  try {
    const body = JSON.parse(bodyJson);
    return JSON.stringify({
      ...body,
      ...(body.stream ? { stream_options: { include_usage: true } } : {}),
    });
  } catch {
    return bodyJson;
  }
}

export function createUsageParserImpl() {
  return {
    parse: (chunk) => {
      if (!chunk.startsWith("data: ")) return;
      try {
        const json = JSON.parse(chunk.slice(6));
        if (json.usage) {
          usageStore = json.usage;
        }
      } catch (e) {
        // Ignore
      }
    },
    retrieve: () => {
      return usageStore ? JSON.stringify(usageStore) : null;
    },
  };
}

export function normalizeUsageImpl(usageJson) {
  try {
    const usage = JSON.parse(usageJson);
    const inputTokens = usage.prompt_tokens ?? 0;
    const outputTokens = usage.completion_tokens ?? 0;
    const reasoningTokens = usage.completion_tokens_details?.reasoning_tokens ?? null;
    const cacheReadTokens = usage.cached_tokens ?? usage.prompt_tokens_details?.cached_tokens ?? null;
    return {
      inputTokens: inputTokens - (cacheReadTokens ?? 0),
      outputTokens,
      reasoningTokens,
      cacheReadTokens,
      cacheWrite5mTokens: null,
      cacheWrite1hTokens: null,
    };
  } catch {
    return {
      inputTokens: 0,
      outputTokens: 0,
      reasoningTokens: null,
      cacheReadTokens: null,
      cacheWrite5mTokens: null,
      cacheWrite1hTokens: null,
    };
  }
}
