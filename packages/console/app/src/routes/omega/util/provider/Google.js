// Google Provider FFI
// JavaScript implementations for Google provider functions
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling

let usageStore = null;

export function modifyHeadersImpl(bodyJson, apiKey) {
  const headers = globalThis._currentHeadersObj;
  if (typeof headers !== "object" || headers === null || !(headers instanceof Headers)) {
    return;
  }
  headers.set("x-goog-api-key", apiKey);
}

export function createUsageParserImpl() {
  return {
    parse: function(chunk) {
      if (typeof chunk !== "string" || chunk.length < 6 || chunk.substring(0, 6) !== "data: ") {
        return;
      }
      try {
        const json = JSON.parse(chunk.slice(6));
        if (typeof json === "object" && json !== null && typeof json.usageMetadata === "object" && json.usageMetadata !== null) {
          usageStore = json.usageMetadata;
        }
      } catch (e) {
        return;
      }
    },
    retrieve: function() {
      if (usageStore === null || typeof usageStore === "undefined") {
        return null;
      }
      try {
        return JSON.stringify(usageStore);
      } catch (e) {
        return null;
      }
    },
  };
}

export function normalizeUsageImpl(usageJson) {
  try {
    const usage = JSON.parse(usageJson);
    if (typeof usage !== "object" || usage === null) {
      return {
        inputTokens: 0,
        outputTokens: 0,
        reasoningTokens: null,
        cacheReadTokens: null,
        cacheWrite5mTokens: null,
        cacheWrite1hTokens: null,
      };
    }

    const promptTokenCount = usage.promptTokenCount;
    const candidatesTokenCount = usage.candidatesTokenCount;
    const thoughtsTokenCount = usage.thoughtsTokenCount;
    const cachedContentTokenCount = usage.cachedContentTokenCount;

    const inputTokens = typeof promptTokenCount === "number" ? promptTokenCount : 0;
    const outputTokens = typeof candidatesTokenCount === "number" ? candidatesTokenCount : 0;
    const reasoningTokens = typeof thoughtsTokenCount === "number" ? thoughtsTokenCount : null;
    const cacheReadTokens = typeof cachedContentTokenCount === "number" ? cachedContentTokenCount : null;

    const cacheReadValue = cacheReadTokens !== null ? cacheReadTokens : 0;
    const finalInputTokens = inputTokens - cacheReadValue;

    return {
      inputTokens: finalInputTokens,
      outputTokens,
      reasoningTokens,
      cacheReadTokens,
      cacheWrite5mTokens: null,
      cacheWrite1hTokens: null,
    };
  } catch (e) {
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
