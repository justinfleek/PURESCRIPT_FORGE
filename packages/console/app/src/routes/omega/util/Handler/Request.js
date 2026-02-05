// Omega Handler Request FFI
// Builds provider requests using provider helper methods
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
// Migrated: 2026-02-04

// Fetch provider request with headers modification
export async function fetchProviderRequest(reqUrl, reqBody, headers, providerInfo) {
  // Headers are already modified by PureScript modifyHeaders call
  // Convert PureScript headers array to Headers object
  const headersObj = new Headers();
  for (const h of headers) {
    headersObj.set(h.key, h.value);
  }
  
  // Remove OpenCode-specific headers (already done in PureScript, but ensure)
  headersObj.delete("host");
  headersObj.delete("content-length");
  headersObj.delete("x-opencode-request");
  headersObj.delete("x-opencode-session");
  headersObj.delete("x-opencode-project");
  headersObj.delete("x-opencode-client");
  
  // Apply header mappings if any
  if (providerInfo.headerMappings) {
    for (const [targetKey, sourceKey] of Object.entries(providerInfo.headerMappings)) {
      const sourceValue = headersObj.get(sourceKey);
      if (sourceValue) {
        headersObj.set(targetKey, sourceValue);
      }
    }
  }
  
  // Make HTTP request
  const response = await fetch(reqUrl, {
    method: "POST",
    headers: headersObj,
    body: reqBody,
  });
  
  // Convert response to PureScript types
  const responseHeaders = [];
  response.headers.forEach((value, key) => {
    responseHeaders.push({ key, value });
  });
  
  const body = await response.text();
  
  return {
    status: response.status,
    statusText: response.statusText,
    headers: responseHeaders,
    body,
  };
}

// Modify headers using provider helper function
// Takes PureScript headers array, body JSON string, apiKey, and modifyHeaders function reference
// Returns modified headers array
export async function modifyHeadersFFI(headers, bodyJson, apiKey, modifyHeadersFn) {
  // Convert PureScript headers array to Headers object
  const headersObj = new Headers();
  for (const h of headers) {
    headersObj.set(h.key, h.value);
  }
  
  // Parse body JSON to object
  let bodyObj;
  try {
    bodyObj = JSON.parse(bodyJson);
  } catch (e) {
    bodyObj = {};
  }
  
  // Call modifyHeaders - it mutates headersObj via FFI
  // Store headersObj reference globally so FFI can access it
  if (typeof globalThis !== "undefined") {
    globalThis._currentHeadersObj = headersObj;
  }
  
  // Call the PureScript modifyHeaders function (wrapped in Effect)
  // It will call modifyHeadersImpl via FFI, which accesses globalThis._currentHeadersObj
  try {
    modifyHeadersFn(bodyJson, apiKey)();
  } catch (e) {
    // Ignore errors
  }
  
  // Reconstruct headers array from mutated Headers object
  const modifiedHeaders = [];
  headersObj.forEach((value, key) => {
    modifiedHeaders.push({ key, value });
  });
  
  // Cleanup
  if (typeof globalThis !== "undefined") {
    delete globalThis._currentHeadersObj;
  }
  
  return modifiedHeaders;
}

// Extract usage from provider response JSON
export function extractUsageFromResponse(format, json) {
  try {
    const data = typeof json === "string" ? JSON.parse(json) : json;
    
    // Extract usage based on format
    if (format === "openai" || format === "oa-compat") {
      return JSON.stringify(data.usage || {});
    } else if (format === "anthropic") {
      return JSON.stringify(data.usage || {});
    } else if (format === "google") {
      return JSON.stringify(data.usageMetadata || {});
    }
    
    return JSON.stringify({});
  } catch (e) {
    return JSON.stringify({});
  }
}

// Convert common request to provider-specific format
export function convertToProviderRequest(format, commonRequestJson, model) {
  try {
    const commonRequest = typeof commonRequestJson === "string" 
      ? JSON.parse(commonRequestJson) 
      : commonRequestJson;
    
    // Add model to request
    const providerRequest = {
      ...commonRequest,
      model,
    };
    
    return JSON.stringify(providerRequest);
  } catch (e) {
    return JSON.stringify({ model, messages: [] });
  }
}
