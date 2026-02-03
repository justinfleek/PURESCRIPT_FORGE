// Rate Limiter FFI Implementation
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

exports.updateFromResponseImpl = function(limiter) {
  return function(headersJson) {
    return function() {
      try {
        var headers = typeof headersJson === "string" ? JSON.parse(headersJson) : headersJson;
        
        // Extract rate limit headers (Venice API format)
        var requestsLimitHeader = headers["x-ratelimit-limit"] !== undefined && headers["x-ratelimit-limit"] !== null ? headers["x-ratelimit-limit"] : headers["X-RateLimit-Limit"];
        var requestsLimit = parseInt(explicitDefault(requestsLimitHeader, "0"), 10);
        var requestsRemainingHeader = headers["x-ratelimit-remaining"] !== undefined && headers["x-ratelimit-remaining"] !== null ? headers["x-ratelimit-remaining"] : headers["X-RateLimit-Remaining"];
        var requestsRemaining = parseInt(explicitDefault(requestsRemainingHeader, "0"), 10);
        var requestsReset = headers["x-ratelimit-reset"] !== undefined && headers["x-ratelimit-reset"] !== null ? headers["x-ratelimit-reset"] : headers["X-RateLimit-Reset"];
        
        var tokensLimitHeader = headers["x-ratelimit-tokens-limit"] !== undefined && headers["x-ratelimit-tokens-limit"] !== null ? headers["x-ratelimit-tokens-limit"] : headers["X-RateLimit-Tokens-Limit"];
        var tokensLimit = parseInt(explicitDefault(tokensLimitHeader, "0"), 10);
        var tokensRemainingHeader = headers["x-ratelimit-tokens-remaining"] !== undefined && headers["x-ratelimit-tokens-remaining"] !== null ? headers["x-ratelimit-tokens-remaining"] : headers["X-RateLimit-Tokens-Remaining"];
        var tokensRemaining = parseInt(explicitDefault(tokensRemainingHeader, "0"), 10);
        var tokensReset = headers["x-ratelimit-tokens-reset"] !== undefined && headers["x-ratelimit-tokens-reset"] !== null ? headers["x-ratelimit-tokens-reset"] : headers["X-RateLimit-Tokens-Reset"];
        
        var tier = headers["x-ratelimit-tier"] !== undefined && headers["x-ratelimit-tier"] !== null ? headers["x-ratelimit-tier"] : headers["X-RateLimit-Tier"];
        
        // Parse reset timestamps
        var requestsResetDate = requestsReset ? new Date(requestsReset * 1000) : null;
        var tokensResetDate = tokensReset ? new Date(tokensReset * 1000) : null;
        
        // Update rate limiter state
        if (limiter && limiter.value) {
          limiter.value = {
            requests: {
              limit: requestsLimit,
              remaining: requestsRemaining,
              reset: requestsResetDate
            },
            tokens: {
              limit: tokensLimit,
              remaining: tokensRemaining,
              reset: tokensResetDate
            },
            tier: explicitDefault(tier, null)
          };
        }
      } catch (e) {
        // Ignore parsing errors - rate limiter will use defaults
        console.error("Failed to update rate limiter:", e);
      }
    };
  };
};
