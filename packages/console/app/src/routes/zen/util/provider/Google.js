// Google Provider FFI
// JavaScript implementations for Google provider functions

let usageStore = null;

export function modifyHeadersImpl(bodyJson, apiKey) {
  const headers = globalThis._currentHeadersObj;
  if (!headers || !(headers instanceof Headers)) {
    return;
  }
  headers.set("x-goog-api-key", apiKey);
}

export function createUsageParserImpl() {
  return {
    parse: (chunk) => {
      if (!chunk.startsWith("data: ")) return;
      try {
        const json = JSON.parse(chunk.slice(6));
        if (json.usageMetadata) {
          usageStore = json.usageMetadata;
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
    const inputTokens = usage.promptTokenCount ?? 0;
    const outputTokens = usage.candidatesTokenCount ?? 0;
    const reasoningTokens = usage.thoughtsTokenCount ?? 0;
    const cacheReadTokens = usage.cachedContentTokenCount ?? 0;
    return {
      inputTokens: inputTokens - cacheReadTokens,
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
