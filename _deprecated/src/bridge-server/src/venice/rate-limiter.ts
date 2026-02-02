/**
 * Rate Limiter for Venice API
 * Implements exponential backoff and rate limit tracking
 */
export interface RateLimitState {
  requests: {
    limit: number;
    remaining: number;
    reset: Date | null;
  };
  tokens: {
    limit: number;
    remaining: number;
    reset: Date | null;
  };
  tier: string | null;
}

export interface RateLimitWarning {
  provider: string;
  tier: string;
  remaining: {
    requests: number;
    tokens: number;
  };
  reset: {
    requests: Date | null;
    tokens: Date | null;
  };
  severity: 'warning' | 'critical' | 'blocked';
}

/**
 * Rate Limiter - Tracks and enforces Venice API rate limits
 */
export class RateLimiter {
  private state: RateLimitState = {
    requests: {
      limit: 0,
      remaining: 0,
      reset: null,
    },
    tokens: {
      limit: 0,
      remaining: 0,
      reset: null,
    },
    tier: null,
  };
  
  private retryAfter: number | null = null;
  private lastRequestTime: number = 0;
  
  /**
   * Check if request can proceed
   */
  canProceed(tier: string): boolean {
    // If we have retry-after, check if enough time has passed
    if (this.retryAfter !== null) {
      const elapsed = Date.now() - this.lastRequestTime;
      if (elapsed < this.retryAfter) {
        return false;
      }
      // Reset retry-after after waiting
      this.retryAfter = null;
    }
    
    // Check rate limits
    if (this.state.requests.remaining <= 0) {
      return false;
    }
    
    if (this.state.tokens.remaining <= 0) {
      return false;
    }
    
    return true;
  }
  
  /**
   * Get wait time if rate limited
   */
  getWaitTime(tier: string): number {
    if (this.retryAfter !== null) {
      const elapsed = Date.now() - this.lastRequestTime;
      return Math.max(0, this.retryAfter - elapsed);
    }
    
    // Check when limits reset
    const now = Date.now();
    let waitTime = 0;
    
    if (this.state.requests.remaining <= 0 && this.state.requests.reset) {
      const resetTime = this.state.requests.reset.getTime();
      waitTime = Math.max(waitTime, resetTime - now);
    }
    
    if (this.state.tokens.remaining <= 0 && this.state.tokens.reset) {
      const resetTime = this.state.tokens.reset.getTime();
      waitTime = Math.max(waitTime, resetTime - now);
    }
    
    return waitTime;
  }
  
  /**
   * Update state from response headers
   */
  updateFromResponse(headers: Headers): void {
    const remainingRequests = parseInt(headers.get('x-ratelimit-remaining-requests') ?? '');
    const limitRequests = parseInt(headers.get('x-ratelimit-limit-requests') ?? '');
    const resetRequests = headers.get('x-ratelimit-reset-requests');
    
    const remainingTokens = parseInt(headers.get('x-ratelimit-remaining-tokens') ?? '');
    const limitTokens = parseInt(headers.get('x-ratelimit-limit-tokens') ?? '');
    const resetTokens = headers.get('x-ratelimit-reset-tokens');
    
    if (!isNaN(remainingRequests) && !isNaN(limitRequests)) {
      this.state.requests = {
        limit: limitRequests,
        remaining: remainingRequests,
        reset: resetRequests ? new Date(resetRequests) : null,
      };
    }
    
    if (!isNaN(remainingTokens) && !isNaN(limitTokens)) {
      this.state.tokens = {
        limit: limitTokens,
        remaining: remainingTokens,
        reset: resetTokens ? new Date(resetTokens) : null,
      };
    }
  }
  
  /**
   * Handle 429 response
   */
  handleRateLimit(retryAfter: number): void {
    this.retryAfter = retryAfter * 1000; // Convert to milliseconds
    this.lastRequestTime = Date.now();
  }
  
  /**
   * Get current state
   */
  getState(): RateLimitState {
    return { ...this.state };
  }
  
  /**
   * Get warning if approaching limits
   */
  getWarning(): RateLimitWarning | null {
    const requestsPercent = this.state.requests.limit > 0
      ? this.state.requests.remaining / this.state.requests.limit
      : 1;
    
    const tokensPercent = this.state.tokens.limit > 0
      ? this.state.tokens.remaining / this.state.tokens.limit
      : 1;
    
    let severity: 'warning' | 'critical' | 'blocked' = 'warning';
    
    if (requestsPercent === 0 || tokensPercent === 0) {
      severity = 'blocked';
    } else if (requestsPercent < 0.1 || tokensPercent < 0.1) {
      severity = 'critical';
    } else if (requestsPercent < 0.2 || tokensPercent < 0.2) {
      severity = 'warning';
    } else {
      return null; // No warning needed
    }
    
    return {
      provider: 'venice',
      tier: this.state.tier ?? 'unknown',
      remaining: {
        requests: this.state.requests.remaining,
        tokens: this.state.tokens.remaining,
      },
      reset: {
        requests: this.state.requests.reset,
        tokens: this.state.tokens.reset,
      },
      severity,
    };
  }
  
  /**
   * Acquire rate limit (wait if needed)
   */
  async acquire(): Promise<void> {
    while (!this.canProceed(this.state.tier ?? 'M')) {
      const waitTime = this.getWaitTime(this.state.tier ?? 'M');
      if (waitTime > 0) {
        await new Promise(resolve => setTimeout(resolve, waitTime));
      } else {
        // Should not happen, but break to avoid infinite loop
        break;
      }
    }
  }
}
