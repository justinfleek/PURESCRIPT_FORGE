// OpenAI-Compatible Provider FFI
// JavaScript implementations for OpenAI-compatible provider functions
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling

let usageStore = null;

export function modifyHeadersImpl(bodyJson, apiKey) {
  const headers = globalThis._currentHeadersObj;
  if (typeof headers !== "object" || headers === null || !(headers instanceof Headers)) {
    return;
  }
  headers.set("authorization", `Bearer ${apiKey}`);
}

export function modifyBodyImpl(bodyJson) {
  if (typeof bodyJson !== "string") {
    return bodyJson;
  }
  try {
    const body = JSON.parse(bodyJson);
    if (typeof body !== "object" || body === null) {
      return bodyJson;
    }

    const bodyStream = body.stream;
    const hasStream = typeof bodyStream === "boolean" && bodyStream === true;

    if (hasStream) {
      const modifiedBody = Object.assign({}, body, {
        stream_options: {
          include_usage: true,
        },
      });
      return JSON.stringify(modifiedBody);
    } else {
      return JSON.stringify(body);
    }
  } catch (e) {
    return bodyJson;
  }
}

export function createUsageParserImpl() {
  return {
    parse: function(chunk) {
      if (typeof chunk !== "string" || chunk.length < 6 || chunk.substring(0, 6) !== "data: ") {
        return;
      }
      try {
        const jsonStr = chunk.substring(6);
        const json = JSON.parse(jsonStr);
        if (typeof json !== "object" || json === null) {
          return;
        }
        if (typeof json.usage === "object" && json.usage !== null) {
          usageStore = json.usage;
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
  if (typeof usageJson !== "string") {
    return {
      inputTokens: 0,
      outputTokens: 0,
      reasoningTokens: null,
      cacheReadTokens: null,
      cacheWrite5mTokens: null,
      cacheWrite1hTokens: null,
    };
  }

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
        inputBytes: 0,
        outputBytes: 0,
        reasoningBytes: null,
        cacheReadBytes: null,
      };
    }

    const promptTokens = usage.prompt_tokens;
    const completionTokens = usage.completion_tokens;
    const inputTokens = typeof promptTokens === "number" ? promptTokens : 0;
    const outputTokens = typeof completionTokens === "number" ? completionTokens : 0;

    const completionTokensDetails = usage.completion_tokens_details;
    let reasoningTokens = null;
    if (typeof completionTokensDetails === "object" && completionTokensDetails !== null) {
      const reasoningTokensValue = completionTokensDetails.reasoning_tokens;
      if (typeof reasoningTokensValue === "number") {
        reasoningTokens = reasoningTokensValue;
      }
    }

    const cachedTokens = usage.cached_tokens;
    const promptTokensDetails = usage.prompt_tokens_details;
    let cacheReadTokens = null;
    if (typeof cachedTokens === "number") {
      cacheReadTokens = cachedTokens;
    } else {
      if (typeof promptTokensDetails === "object" && promptTokensDetails !== null) {
        const cachedTokensValue = promptTokensDetails.cached_tokens;
        if (typeof cachedTokensValue === "number") {
          cacheReadTokens = cachedTokensValue;
        }
      }
    }

    const cacheReadValue = cacheReadTokens !== null ? cacheReadTokens : 0;
    const finalInputTokens = inputTokens - cacheReadValue;

    return {
      inputTokens: finalInputTokens,
      outputTokens,
      reasoningTokens,
      cacheReadTokens,
      cacheWrite5mTokens: null,
      cacheWrite1hTokens: null,
      inputBytes: 0,
      outputBytes: 0,
      reasoningBytes: null,
      cacheReadBytes: null,
    };
  } catch (e) {
    return {
      inputTokens: 0,
      outputTokens: 0,
      reasoningTokens: null,
      cacheReadTokens: null,
      cacheWrite5mTokens: null,
      cacheWrite1hTokens: null,
      inputBytes: 0,
      outputBytes: 0,
      reasoningBytes: null,
      cacheReadBytes: null,
    };
  }
}
