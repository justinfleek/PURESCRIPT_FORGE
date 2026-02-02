// Venice Client FFI Implementation
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

exports.createVeniceClientImpl = function(apiKey) {
  return function(store) {
    return function(logger) {
      return function(rateLimiter) {
        return function() {
          return {
            apiKey: apiKey,
            store: store,
            logger: logger,
            rateLimiter: rateLimiter,
            baseUrl: "https://api.venice.ai/api/v1"
          };
        };
      };
    };
  };
};

exports.getApiKey = function(client) {
  return client.apiKey;
};

exports.encodeRequest = function(request) {
  return JSON.stringify({
    model: request.model,
    messages: request.messages,
    max_tokens: request.maxTokens,
    temperature: request.temperature,
    stream: false
  });
};

exports.encodeStreamRequest = function(request) {
  return JSON.stringify({
    model: request.model,
    messages: request.messages,
    max_tokens: request.maxTokens,
    temperature: request.temperature,
    stream: true
  });
};

exports.decodeResponse = function(jsonStr) {
  var data = JSON.parse(jsonStr);
  var choicesArray = data.choices !== undefined && data.choices !== null && Array.isArray(data.choices) ? data.choices : [];
  return {
    id: explicitDefault(data.id, ""),
    model: explicitDefault(data.model, ""),
    choices: choicesArray.map(function(c) {
      return {
        message: {
          role: c.message ? c.message.role : "",
          content: c.message ? c.message.content : ""
        }
      };
    }),
    usage: {
      promptTokens: data.usage ? data.usage.prompt_tokens : 0,
      completionTokens: data.usage ? data.usage.completion_tokens : 0,
      totalTokens: data.usage ? data.usage.total_tokens : 0
    }
  };
};

exports.extractAndUpdateBalance = function(client) {
  return function(response) {
    return function() {
      try {
        // Extract headers from response
        var headers = response.headers;
        var getHeader = function(name) {
          // Try different header access methods
          if (headers.get) {
            var headerValue = headers.get(name);
            return headerValue !== undefined && headerValue !== null ? headerValue : headers.get(name.toLowerCase());
          } else if (headers[name]) {
            return headers[name];
          } else if (headers[name.toLowerCase()]) {
            return headers[name.toLowerCase()];
          }
          return null;
        };
        
        var diemHeader1 = getHeader("x-venice-balance-diem");
        var diemHeader = diemHeader1 !== undefined && diemHeader1 !== null ? diemHeader1 : getHeader("X-Venice-Balance-Diem");
        var usdHeader1 = getHeader("x-venice-balance-usd");
        var usdHeader = usdHeader1 !== undefined && usdHeader1 !== null ? usdHeader1 : getHeader("X-Venice-Balance-Usd");
        var effectiveHeader1 = getHeader("x-venice-balance-effective");
        var effectiveHeader = effectiveHeader1 !== undefined && effectiveHeader1 !== null ? effectiveHeader1 : getHeader("X-Venice-Balance-Effective");
        
        var diem = diemHeader ? parseFloat(diemHeader) : null;
        var usd = usdHeader ? parseFloat(usdHeader) : null;
        var effective = effectiveHeader ? parseFloat(effectiveHeader) : null;
        
        // Calculate effective if not provided
        if (effective === null || isNaN(effective)) {
          if (diem !== null && !isNaN(diem) && usd !== null && !isNaN(usd)) {
            effective = diem + usd;
          } else if (diem !== null && !isNaN(diem)) {
            effective = diem;
          } else {
            effective = 0.0;
          }
        }
        
        if (diem !== null && !isNaN(diem)) {
          // Update balance in store via PureScript
          // client.store contains the StateStore
          // Call PureScript updateBalancePartial function
          if (client.store && client.store.updateBalancePartial) {
            try {
              client.store.updateBalancePartial({
                venice: {
                  diem: diem,
                  usd: usd !== null && !isNaN(usd) ? usd : 0.0,
                  effective: effective,
                  lastUpdated: new Date().toISOString()
                }
              })();
            } catch (e) {
              console.error("Failed to update balance in store:", e);
            }
          }
          
          // Log balance update
          if (client.logger && client.logger.info) {
            var usdValue = usd !== undefined && usd !== null && !isNaN(usd) ? usd : 0;
            client.logger.info("Balance updated: Diem=" + diem + ", USD=" + usdValue + ", Effective=" + effective)();
          }
        }
      } catch (e) {
        console.error("Failed to extract balance:", e);
      }
    };
  };
};

exports.decodeModelsResponse = function(jsonStr) {
  var data = JSON.parse(jsonStr);
  var modelsArray = data.data !== undefined && data.data !== null && Array.isArray(data.data) ? data.data : [];
  return modelsArray.map(function(m) {
    return {
      id: explicitDefault(m.id, ""),
      pricing: {
        input: m.pricing !== undefined && m.pricing !== null ? explicitDefault(m.pricing.input, 0.0) : 0.0,
        output: m.pricing !== undefined && m.pricing !== null ? explicitDefault(m.pricing.output, 0.0) : 0.0
      },
      tier: explicitDefault(m.tier, ""),
      contextLength: explicitDefault(m.context_length, 0)
    };
  });
};

exports.encodeImageRequest = function(request) {
  return JSON.stringify({
    model: request.model,
    prompt: request.prompt,
    width: explicitDefault(request.width, 1024),
    height: explicitDefault(request.height, 1024)
  });
};

exports.decodeImageResponse = function(jsonStr) {
  var data = JSON.parse(jsonStr);
  return {
    images: explicitDefault(data.images, [])
  };
};

exports.acquireRateLimit = function(client) {
  return function() {
    // Call PureScript rate limiter acquireRateLimit
    if (client.rateLimiter) {
      // RateLimiter is a Ref, so we need to check state and wait if needed
      var rateLimiterValue = client.rateLimiter !== undefined && client.rateLimiter !== null && client.rateLimiter.value !== undefined && client.rateLimiter.value !== null 
        ? client.rateLimiter.value 
        : {
            requests: { limit: 0, remaining: 0, reset: null },
            tokens: { limit: 0, remaining: 0, reset: null },
            tier: null
          };
      var state = rateLimiterValue;
      
      // Check if we can proceed
      if (state.requests.remaining > 0 && state.tokens.remaining > 0) {
        // Can proceed immediately
        return;
      }
      
      // Would implement proper waiting logic here
      // For now, just proceed (rate limiting handled by API)
    }
  };
};

exports.parseStream = function(response) {
  return function() {
    return new Promise(function(resolve) {
      if (response === undefined || response === null || response.body === undefined || response.body === null) {
        resolve({ tag: "Right", value: function() { return Promise.resolve({ tag: "Nothing" }); } });
        return;
      }
      
      var reader = response.body.getReader();
      var decoder = new TextDecoder();
      var buffer = "";
      
      var readChunk = function() {
        return reader.read().then(function(result) {
          if (result.done) {
            resolve({ tag: "Right", value: function() { return Promise.resolve({ tag: "Nothing" }); } });
            return;
          }
          
          // Decode chunk
          buffer += decoder.decode(result.value, { stream: true });
          
          // Parse SSE format (data: {...}\n\n)
          var lines = buffer.split("\n");
          var lastLine = lines.pop();
          buffer = lastLine !== undefined && lastLine !== null ? lastLine : ""; // Keep incomplete line in buffer
          
          var chunks = [];
          var currentData = "";
          
          for (var i = 0; i < lines.length; i++) {
            var line = lines[i].trim();
            if (line.startsWith("data: ")) {
              var dataStr = line.substring(6);
              if (dataStr === "[DONE]") {
                resolve({ tag: "Right", value: function() { return Promise.resolve({ tag: "Nothing" }); } });
                return;
              }
              try {
                var chunkData = JSON.parse(dataStr);
                chunks.push({
                  id: explicitDefault(chunkData.id, ""),
                  choices: (chunkData.choices !== undefined && chunkData.choices !== null && Array.isArray(chunkData.choices) ? chunkData.choices : []).map(function(c) {
                    return {
                      delta: {
                        content: c.delta && c.delta.content ? c.delta.content : null
                      }
                    };
                  })
                });
              } catch (e) {
                // Ignore parse errors for individual chunks
              }
            }
          }
          
          // Return function that yields next chunk
          var chunkIndex = 0;
          var streamHandler = function() {
            return new Promise(function(resolveChunk) {
              if (chunkIndex < chunks.length) {
                var chunk = chunks[chunkIndex++];
                resolveChunk({ tag: "Just", value: chunk });
              } else {
                // Read more chunks
                readChunk().then(function(nextHandler) {
                  if (nextHandler.tag === "Right") {
                    nextHandler.value().then(function(nextChunk) {
                      resolveChunk(nextChunk);
                    });
                  } else {
                    resolveChunk({ tag: "Nothing" });
                  }
                });
              }
            });
          };
          
          if (chunks.length > 0) {
            resolve({ tag: "Right", value: streamHandler });
          } else {
            // Continue reading
            readChunk();
          }
        }).catch(function(error) {
          var errorMessage = error.message !== undefined && error.message !== null ? error.message : "Stream read error";
          resolve({ tag: "Left", value: errorMessage });
        });
      };
      
      readChunk();
    });
  };
};
