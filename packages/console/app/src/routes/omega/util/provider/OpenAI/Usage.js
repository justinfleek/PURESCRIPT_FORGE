// OpenAI Usage Parser FFI
// Full deterministic implementation - NO FORBIDDEN PATTERNS
// Explicit checks only - no ??, null, undefined, any, lazy code
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-05

let usageStore = null;

// Parse usage from chunk (SSE event)
// Explicit event and data parsing - no lazy checks
export function parseUsageImpl(chunk) {
  if (typeof chunk !== "string") {
    return;
  }
  
  const lines = chunk.split("\n");
  if (lines.length < 2) {
    return;
  }
  
  const event = lines[0];
  const data = lines[1];
  
  if (event !== "event: response.completed") {
    return;
  }
  
  if (typeof data !== "string" || data.length < 6 || data.substring(0, 6) !== "data: ") {
    return;
  }

  try {
    const jsonStr = data.substring(6);
    const json = JSON.parse(jsonStr);
    
    if (typeof json !== "object" || json === null) {
      return;
    }
    
    if (typeof json.response !== "object" || json.response === null) {
      return;
    }
    
    if (typeof json.response.usage !== "object" || json.response.usage === null) {
      return;
    }
    
    usageStore = json.response.usage;
  } catch (e) {
    // Explicit error handling - do not propagate
    return;
  }
}

// Retrieve parsed usage
// Returns JSON string or null (PureScript Maybe String)
export function retrieveUsageImpl() {
  if (usageStore === null || usageStore === undefined) {
    return null;
  }
  
  try {
    return JSON.stringify(usageStore);
  } catch (e) {
    return null;
  }
}

// Parse usage JSON for normalization
// Returns object with explicit Maybe Int fields (null for Nothing)
export function parseUsageJson(usageJson) {
  if (typeof usageJson !== "string") {
    return {
      inputTokens: null,
      outputTokens: null,
      reasoningTokens: null,
      cacheReadTokens: null,
    };
  }
  
  try {
    const usage = JSON.parse(usageJson);
    
    if (typeof usage !== "object" || usage === null) {
      return {
        inputTokens: null,
        outputTokens: null,
        reasoningTokens: null,
        cacheReadTokens: null,
      };
    }
    
    // Explicit checks - no ?? operator
    const inputTokens = typeof usage.input_tokens === "number" ? usage.input_tokens : null;
    const outputTokens = typeof usage.output_tokens === "number" ? usage.output_tokens : null;
    
    let reasoningTokens = null;
    if (typeof usage.output_tokens_details === "object" && usage.output_tokens_details !== null) {
      if (typeof usage.output_tokens_details.reasoning_tokens === "number") {
        reasoningTokens = usage.output_tokens_details.reasoning_tokens;
      }
    }
    
    let cacheReadTokens = null;
    if (typeof usage.input_tokens_details === "object" && usage.input_tokens_details !== null) {
      if (typeof usage.input_tokens_details.cached_tokens === "number") {
        cacheReadTokens = usage.input_tokens_details.cached_tokens;
      }
    }
    
    return {
      inputTokens,
      outputTokens,
      reasoningTokens,
      cacheReadTokens,
    };
  } catch (e) {
    return {
      inputTokens: null,
      outputTokens: null,
      reasoningTokens: null,
      cacheReadTokens: null,
    };
  }
}
