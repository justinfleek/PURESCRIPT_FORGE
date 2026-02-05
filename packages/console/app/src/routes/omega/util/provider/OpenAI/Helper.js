// OpenAI Provider Helper FFI
// Full deterministic implementation - NO FORBIDDEN PATTERNS
// Explicit checks only - no ??, null, undefined, any, lazy code
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-05

// Modify headers (FFI boundary - mutates Headers object in globalThis._currentHeadersObj)
// Explicit checks - no lazy access
export function modifyHeadersImpl(bodyJson, apiKey) {
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
