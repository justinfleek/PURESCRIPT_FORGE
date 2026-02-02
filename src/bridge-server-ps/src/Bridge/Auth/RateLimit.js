// Rate Limiting FFI - Token bucket algorithm implementation
// Production-grade per-user rate limiting

// Token bucket refill logic
function refillBucket(bucket, config, now) {
  const elapsed = (now - bucket.lastRefill.milliseconds) / 1000; // Convert to seconds
  const refillAmount = Math.floor((config.refillRate * elapsed) / config.windowSeconds);
  const newTokens = Math.min(config.maxRequests, bucket.tokens + refillAmount);
  return {
    tokens: newTokens,
    lastRefill: bucket.lastRefill
  };
}

// Helper: Get config from Map (PureScript Map is an object with value property)
function getConfig(operation, configs) {
  if (configs && configs.value) {
    const map = configs.value;
    if (map && map[operation]) {
      return map[operation];
    }
  }
  return null;
}

// Helper: Get bucket from Map
function getBucket(key, buckets) {
  if (buckets && buckets.value) {
    const map = buckets.value;
    if (map && map[key]) {
      return map[key];
    }
  }
  return null;
}

// Helper: Set bucket in Map
function setBucket(key, bucket, buckets) {
  if (buckets && buckets.value) {
    const map = buckets.value;
    map[key] = bucket;
    return buckets;
  }
  return { value: { [key]: bucket } };
}

// Check rate limit
export const checkRateLimitImpl = function(userId) {
  return function(operation) {
    return function(rateLimiter) {
      return function() {
        try {
          const bucketsRef = rateLimiter.buckets;
          const buckets = bucketsRef.read();
          const config = getConfig(operation, rateLimiter.configs);
          
          if (!config) {
            // No rate limit for this operation
            return {
              tag: 'Right',
              value: {
                allowed: true,
                remaining: 999999,
                resetAt: null,
                error: null
              }
            };
          }
          
          const key = userId + ":" + operation;
          const now = Date.now();
          const nowInstant = { milliseconds: now };
          
          const bucket = getBucket(key, buckets);
          const currentBucket = bucket
            ? refillBucket(bucket, config, now)
            : { tokens: config.maxRequests, lastRefill: nowInstant };
          
          if (currentBucket.tokens > 0) {
            // Allow request, consume token
            const newBucket = { tokens: currentBucket.tokens - 1, lastRefill: currentBucket.lastRefill };
            const newBuckets = setBucket(key, newBucket, buckets);
            bucketsRef.write(newBuckets);
            
            const resetAt = currentBucket.lastRefill.milliseconds + (config.windowSeconds * 1000);
            
            return {
              tag: 'Right',
              value: {
                allowed: true,
                remaining: newBucket.tokens,
                resetAt: { milliseconds: resetAt },
                error: null
              }
            };
          } else {
            // Rate limit exceeded
            const resetAt = currentBucket.lastRefill.milliseconds + (config.windowSeconds * 1000);
            
            return {
              tag: 'Left',
              value: "Rate limit exceeded for " + operation
            };
          }
        } catch (e) {
          return {
            tag: 'Left',
            value: 'Rate limit check error: ' + e.message
          };
        }
      };
    };
  };
};

// Reset rate limit
export const resetRateLimitImpl = function(userId) {
  return function(operation) {
    return function(rateLimiter) {
      return function() {
        try {
          const bucketsRef = rateLimiter.buckets;
          const buckets = bucketsRef.read();
          const key = userId + ":" + operation;
          const config = getConfig(operation, rateLimiter.configs);
          
          if (!config) {
            return { tag: 'Left', value: 'No rate limit config for operation' };
          }
          
          const now = Date.now();
          const newBucket = { tokens: config.maxRequests, lastRefill: { milliseconds: now } };
          const newBuckets = setBucket(key, newBucket, buckets);
          bucketsRef.write(newBuckets);
          
          return { tag: 'Right', value: {} };
        } catch (e) {
          return { tag: 'Left', value: 'Rate limit reset error: ' + e.message };
        }
      };
    };
  };
};

// Get rate limit status
export const getRateLimitStatusImpl = function(userId) {
  return function(operation) {
    return function(rateLimiter) {
      return function() {
        try {
          const buckets = rateLimiter.buckets.read();
          const config = getConfig(operation, rateLimiter.configs);
          
          if (!config) {
            return {
              allowed: true,
              remaining: 999999,
              resetAt: null,
              error: null
            };
          }
          
          const key = userId + ":" + operation;
          const now = Date.now();
          const bucket = getBucket(key, buckets);
          
          if (!bucket) {
            return {
              allowed: true,
              remaining: config.maxRequests,
              resetAt: null,
              error: null
            };
          }
          
          const currentBucket = refillBucket(bucket, config, now);
          const resetAt = currentBucket.lastRefill.milliseconds + (config.windowSeconds * 1000);
          
          return {
            allowed: currentBucket.tokens > 0,
            remaining: currentBucket.tokens,
            resetAt: { milliseconds: resetAt },
            error: null
          };
        } catch (e) {
          return {
            allowed: false,
            remaining: 0,
            resetAt: null,
            error: 'Rate limit status error: ' + e.message
          };
        }
      };
    };
  };
};
