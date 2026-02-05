// Google Provider Helper FFI
// Full deterministic implementation - NO FORBIDDEN PATTERNS
// Explicit checks only - no ??, null, undefined, any, lazy code
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/google.ts
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
  
  headers.set("x-goog-api-key", apiKey);
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
        
        if (typeof json.usageMetadata !== "object" || json.usageMetadata === null) {
          return;
        }
        
        usageStore = json.usageMetadata;
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

// Normalize usage from Google format to common format
// Explicit checks - no ?? operator, no undefined
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
    const inputTokens = typeof usage.promptTokenCount === "number" ? usage.promptTokenCount : 0;
    const outputTokens = typeof usage.candidatesTokenCount === "number" ? usage.candidatesTokenCount : 0;
    
    let reasoningTokens = null;
    if (typeof usage.thoughtsTokenCount === "number") {
      reasoningTokens = usage.thoughtsTokenCount;
    }
    
    let cacheReadTokens = null;
    if (typeof usage.cachedContentTokenCount === "number") {
      cacheReadTokens = usage.cachedContentTokenCount;
    }
    
    // Explicit calculation - no lazy subtraction
    const finalInputTokens = inputTokens - (cacheReadTokens !== null ? cacheReadTokens : 0);
    
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
