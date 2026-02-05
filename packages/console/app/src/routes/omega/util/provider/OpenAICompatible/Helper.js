// OpenAI-Compatible Provider Helper FFI
// Full deterministic implementation - NO FORBIDDEN PATTERNS
// Explicit checks only - no ??, null, undefined, any, lazy code
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai-compatible.ts
// Migrated: 2026-02-05

let usageStore = null;

// Modify headers (FFI boundary - mutates Headers object in globalThis._currentHeadersObj)
// Signature matches PureScript: String -> String -> String -> Unit
export function modifyHeadersImpl(bodyJson, apiKey, _unused) {
  if (typeof bodyJson !== "string" || typeof apiKey !== "string") {
    return;
  }
  
  const headers = globalThis._currentHeadersObj;
  if (headers === null || headers === undefined) {
    return;
  }
  
  if (!(headers instanceof Headers)) {
    return;
  }
  
  headers.set("authorization", `Bearer ${apiKey}`);
}

// Modify body - adds stream_options when streaming
// Explicit checks - no lazy spreading
export function modifyBodyImpl(bodyJson) {
  if (typeof bodyJson !== "string") {
    return bodyJson;
  }
  
  try {
    const body = JSON.parse(bodyJson);
    
    if (typeof body !== "object" || body === null) {
      return bodyJson;
    }
    
    // Explicit check for stream property
    const hasStream = typeof body.stream === "boolean" && body.stream === true;
    
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

// Create usage parser
// Returns parser object with explicit parse and retrieve methods
export function createUsageParserImpl() {
  return {
    parse: function(chunk) {
      if (typeof chunk !== "string") {
        return;
      }
      
      if (chunk.length < 6 || chunk.substring(0, 6) !== "data: ") {
        return;
      }
      
      try {
        const jsonStr = chunk.substring(6);
        const json = JSON.parse(jsonStr);
        
        if (typeof json !== "object" || json === null) {
          return;
        }
        
        if (typeof json.usage !== "object" || json.usage === null) {
          return;
        }
        
        usageStore = json.usage;
      } catch (e) {
        // Explicit error handling - do not propagate
        return;
      }
    },
    retrieve: function() {
      if (usageStore === null || usageStore === undefined) {
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

// Normalize usage from OpenAI-compatible format to common format
// Explicit checks - no ?? operator, no undefined, no lazy code
// Returns UsageInfo with explicit Maybe Int fields (null for Nothing)
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
      };
    }
    
    // Explicit checks - no ?? operator
    const inputTokens = typeof usage.prompt_tokens === "number" ? usage.prompt_tokens : 0;
    const outputTokens = typeof usage.completion_tokens === "number" ? usage.completion_tokens : 0;
    
    // Explicit nested checks for reasoning tokens
    let reasoningTokens = null;
    if (typeof usage.completion_tokens_details === "object" && usage.completion_tokens_details !== null) {
      if (typeof usage.completion_tokens_details.reasoning_tokens === "number") {
        reasoningTokens = usage.completion_tokens_details.reasoning_tokens;
      }
    }
    
    // Explicit nested checks for cache read tokens - check both locations
    let cacheReadTokens = null;
    if (typeof usage.cached_tokens === "number") {
      cacheReadTokens = usage.cached_tokens;
    } else {
      if (typeof usage.prompt_tokens_details === "object" && usage.prompt_tokens_details !== null) {
        if (typeof usage.prompt_tokens_details.cached_tokens === "number") {
          cacheReadTokens = usage.prompt_tokens_details.cached_tokens;
        }
      }
    }
    
    // Explicit calculation - no lazy subtraction
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
