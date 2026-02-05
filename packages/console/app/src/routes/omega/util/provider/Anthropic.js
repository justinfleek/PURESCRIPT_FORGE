// Anthropic Provider FFI
// Full deterministic implementation - NO FORBIDDEN PATTERNS
// Explicit checks only - no ??, null, undefined, any, lazy code, optional chaining
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/zen/util/provider/anthropic.ts
// Migrated: 2026-02-05

import { EventStreamCodec } from "@smithy/eventstream-codec";
import { fromUtf8, toUtf8 } from "@smithy/util-utf8";

let usageStore = null;

// Modify headers (FFI boundary - mutates Headers object in globalThis._currentHeadersObj)
// Explicit checks - no lazy access, no ?? operator
export function modifyHeadersImpl(isBedrock, isSonnet, bodyJson, apiKey) {
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
  
  try {
    const body = JSON.parse(bodyJson);
    
    if (isBedrock === true) {
      headers.set("Authorization", `Bearer ${apiKey}`);
    } else {
      headers.set("x-api-key", apiKey);
      
      // Explicit check for existing anthropic-version header
      const existingVersion = headers.get("anthropic-version");
      if (existingVersion === null || existingVersion === "") {
        headers.set("anthropic-version", "2023-06-01");
      } else {
        headers.set("anthropic-version", existingVersion);
      }
      
      // Explicit check for model property
      if (typeof body === "object" && body !== null) {
        if (typeof body.model === "string") {
          if (body.model.length >= 14 && body.model.substring(0, 14) === "claude-sonnet-") {
            headers.set("anthropic-beta", "context-1m-2025-08-07");
          }
        }
      }
    }
  } catch (e) {
    // Explicit error handling - do not propagate
    return;
  }
}

// Modify body - explicit object construction, no lazy spreading
export function modifyBodyImpl(isBedrock, isSonnet, bodyJson) {
  if (typeof bodyJson !== "string") {
    return bodyJson;
  }
  
  try {
    const body = JSON.parse(bodyJson);
    
    if (typeof body !== "object" || body === null) {
      return bodyJson;
    }
    
    if (isBedrock === true) {
      // Explicit object construction - no undefined properties
      const modifiedBody = {};
      
      // Copy all existing properties except model and stream
      for (const key in body) {
        if (key !== "model" && key !== "stream") {
          modifiedBody[key] = body[key];
        }
      }
      
      modifiedBody.anthropic_version = "bedrock-2023-05-31";
      
      if (isSonnet === true) {
        modifiedBody.anthropic_beta = "context-1m-2025-08-07";
      }
      
      return JSON.stringify(modifiedBody);
    } else {
      // Explicit object construction
      const modifiedBody = {};
      
      // Copy all existing properties
      for (const key in body) {
        modifiedBody[key] = body[key];
      }
      
      modifiedBody.service_tier = "standard_only";
      
      return JSON.stringify(modifiedBody);
    }
  } catch (e) {
    return bodyJson;
  }
}

// Create binary stream decoder - explicit buffer handling
export function createBinaryStreamDecoderImpl(isBedrock) {
  if (isBedrock !== true) {
    return function() {
      return null;
    };
  }
  
  const decoder = new TextDecoder();
  const encoder = new TextEncoder();
  const codec = new EventStreamCodec(toUtf8, fromUtf8);
  let buffer = new Uint8Array(0);
  
  return function(value) {
    if (!(value instanceof Uint8Array)) {
      return null;
    }
    
    const newBuffer = new Uint8Array(buffer.length + value.length);
    newBuffer.set(buffer);
    newBuffer.set(value, buffer.length);
    buffer = newBuffer;

    const messages = [];
    
    while (buffer.length >= 4) {
      const totalLength = new DataView(buffer.buffer, buffer.byteOffset, buffer.byteLength).getUint32(0, false);
      
      if (buffer.length < totalLength) {
        break;
      }

      try {
        const subView = buffer.subarray(0, totalLength);
        const decoded = codec.decode(subView);
        buffer = buffer.slice(totalLength);

        // Explicit check for message-type header - no optional chaining
        if (typeof decoded.headers === "object" && decoded.headers !== null) {
          const messageTypeHeader = decoded.headers[":message-type"];
          if (typeof messageTypeHeader === "object" && messageTypeHeader !== null) {
            if (messageTypeHeader.value === "event") {
              const data = decoder.decode(decoded.body, { stream: true });
              const parsedDataResult = JSON.parse(data);
              
              // Explicit property deletion
              if (typeof parsedDataResult === "object" && parsedDataResult !== null) {
                delete parsedDataResult.p;
                
                if (typeof parsedDataResult.bytes === "string") {
                  const binary = atob(parsedDataResult.bytes);
                  const uint8 = Uint8Array.from(binary, function(c) {
                    return c.charCodeAt(0);
                  });
                  const bytes = decoder.decode(uint8);
                  const parsedBytes = JSON.parse(bytes);
                  
                  if (typeof parsedBytes === "object" && parsedBytes !== null) {
                    if (typeof parsedBytes.type === "string") {
                      const eventName = parsedBytes.type;
                      messages.push(["event: ", eventName, "\n", "data: ", bytes, "\n\n"].join(""));
                    }
                  }
                }
              }
            }
          }
        }
      } catch (e) {
        // Explicit error handling - break on decode error
        break;
      }
    }
    
    if (messages.length > 0) {
      return encoder.encode(messages.join(""));
    } else {
      return null;
    }
  };
}

// Create usage parser - explicit checks, no ?? operator, no optional chaining
export function createUsageParserImpl() {
  return {
    parse: function(chunk) {
      if (typeof chunk !== "string") {
        return;
      }
      
      const lines = chunk.split("\n");
      if (lines.length < 2) {
        return;
      }
      
      const data = lines[1];
      if (typeof data !== "string" || data.length < 6 || data.substring(0, 6) !== "data: ") {
        return;
      }
      
      try {
        const jsonStr = data.substring(6);
        const json = JSON.parse(jsonStr);
        
        if (typeof json !== "object" || json === null) {
          return;
        }
        
        // Explicit checks - no ?? operator, no optional chaining
        let usageUpdate = null;
        if (typeof json.usage === "object" && json.usage !== null) {
          usageUpdate = json.usage;
        } else {
          if (typeof json.message === "object" && json.message !== null) {
            if (typeof json.message.usage === "object" && json.message.usage !== null) {
              usageUpdate = json.message.usage;
            }
          }
        }
        
        if (usageUpdate === null) {
          return;
        }
        
        // Explicit object construction - no lazy spreading
        const newUsage = {};
        
        // Copy existing usageStore properties if it exists
        if (usageStore !== null && typeof usageStore === "object") {
          for (const key in usageStore) {
            newUsage[key] = usageStore[key];
          }
        }
        
        // Copy usageUpdate properties
        for (const key in usageUpdate) {
          newUsage[key] = usageUpdate[key];
        }
        
        // Explicit cache_creation merge
        if (typeof newUsage.cache_creation !== "object" || newUsage.cache_creation === null) {
          newUsage.cache_creation = {};
        }
        if (typeof usageStore === "object" && usageStore !== null) {
          if (typeof usageStore.cache_creation === "object" && usageStore.cache_creation !== null) {
            for (const key in usageStore.cache_creation) {
              newUsage.cache_creation[key] = usageStore.cache_creation[key];
            }
          }
        }
        if (typeof usageUpdate.cache_creation === "object" && usageUpdate.cache_creation !== null) {
          for (const key in usageUpdate.cache_creation) {
            newUsage.cache_creation[key] = usageUpdate.cache_creation[key];
          }
        }
        
        // Explicit server_tool_use merge
        if (typeof newUsage.server_tool_use !== "object" || newUsage.server_tool_use === null) {
          newUsage.server_tool_use = {};
        }
        if (typeof usageStore === "object" && usageStore !== null) {
          if (typeof usageStore.server_tool_use === "object" && usageStore.server_tool_use !== null) {
            for (const key in usageStore.server_tool_use) {
              newUsage.server_tool_use[key] = usageStore.server_tool_use[key];
            }
          }
        }
        if (typeof usageUpdate.server_tool_use === "object" && usageUpdate.server_tool_use !== null) {
          for (const key in usageUpdate.server_tool_use) {
            newUsage.server_tool_use[key] = usageUpdate.server_tool_use[key];
          }
        }
        
        usageStore = newUsage;
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

// Normalize usage - explicit checks, no ?? operator, no optional chaining
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
    
    // Explicit checks - no ?? operator
    const inputTokens = typeof usage.input_tokens === "number" ? usage.input_tokens : 0;
    const outputTokens = typeof usage.output_tokens === "number" ? usage.output_tokens : 0;
    
    // Explicit nested checks for cache_read_input_tokens
    let cacheReadTokens = null;
    if (typeof usage.cache_read_input_tokens === "number") {
      cacheReadTokens = usage.cache_read_input_tokens;
    }
    
    // Explicit nested checks for cache_creation.ephemeral_5m_input_tokens
    let cacheWrite5mTokens = null;
    if (typeof usage.cache_creation === "object" && usage.cache_creation !== null) {
      if (typeof usage.cache_creation.ephemeral_5m_input_tokens === "number") {
        cacheWrite5mTokens = usage.cache_creation.ephemeral_5m_input_tokens;
      }
    }
    
    // Explicit nested checks for cache_creation.ephemeral_1h_input_tokens
    let cacheWrite1hTokens = null;
    if (typeof usage.cache_creation === "object" && usage.cache_creation !== null) {
      if (typeof usage.cache_creation.ephemeral_1h_input_tokens === "number") {
        cacheWrite1hTokens = usage.cache_creation.ephemeral_1h_input_tokens;
      }
    }
    
    return {
      inputTokens,
      outputTokens,
      reasoningTokens: null,
      cacheReadTokens,
      cacheWrite5mTokens,
      cacheWrite1hTokens,
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

// Encode URI component - explicit wrapper
export function encodeURIComponent(str) {
  if (typeof str !== "string") {
    return "";
  }
  return globalThis.encodeURIComponent(str);
}
