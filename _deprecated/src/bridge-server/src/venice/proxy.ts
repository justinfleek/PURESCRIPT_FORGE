/**
 * Venice API Proxy
 * Production-grade Venice API client with balance extraction
 */
import { StateStore } from '../state/store.js';
import { RateLimiter } from './rate-limiter.js';

export interface ChatCompletionRequest {
  model: string;
  messages: Array<{
    role: 'system' | 'user' | 'assistant';
    content: string;
  }>;
  max_tokens?: number;
  temperature?: number;
  top_p?: number;
  stream?: boolean;
  stop?: string | string[];
  presence_penalty?: number;
  frequency_penalty?: number;
}

export interface ChatCompletionResponse {
  id: string;
  object: 'chat.completion';
  created: number;
  model: string;
  choices: Array<{
    index: number;
    message: {
      role: string;
      content: string;
    };
    finish_reason: 'stop' | 'length' | 'content_filter';
  }>;
  usage: {
    prompt_tokens: number;
    completion_tokens: number;
    total_tokens: number;
  };
}

export interface VeniceResponseMeta {
  balance: {
    diem: number;
    usd: number;
  };
  rateLimits: {
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
  };
}

export class VeniceApiError extends Error {
  constructor(
    public status: number,
    public type: string,
    message: string,
    public code?: string
  ) {
    super(message);
    this.name = 'VeniceApiError';
  }
  
  isRetryable(): boolean {
    return this.status === 429 || this.status >= 500;
  }
}

/**
 * Venice Proxy - Proxies Venice API requests and extracts balance
 */
export class VeniceProxy {
  private apiKey: string;
  private store: StateStore;
  private rateLimiter: RateLimiter;
  private baseUrl = 'https://api.venice.ai/api/v1';
  
  constructor(apiKey: string, store: StateStore) {
    this.apiKey = apiKey;
    this.store = store;
    this.rateLimiter = new RateLimiter();
  }
  
  /**
   * Chat completion request
   */
  async chat(request: ChatCompletionRequest): Promise<ChatCompletionResponse> {
    // Acquire rate limit
    await this.rateLimiter.acquire();
    
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(request),
    });
    
    // Extract balance from EVERY response
    this.extractAndUpdateBalance(response.headers);
    
    // Update rate limiter from headers
    this.rateLimiter.updateFromResponse(response.headers);
    
    // Handle rate limit errors
    if (response.status === 429) {
      const retryAfter = parseInt(response.headers.get('retry-after') ?? '1');
      this.rateLimiter.handleRateLimit(retryAfter);
      throw await this.handleError(response);
    }
    
    if (!response.ok) {
      throw await this.handleError(response);
    }
    
    return response.json();
  }
  
  /**
   * Extract balance and rate limits from response headers
   * CRITICAL: Called on EVERY Venice API response
   */
  private extractAndUpdateBalance(headers: Headers): void {
    const diem = parseFloat(headers.get('x-venice-balance-diem') ?? '');
    const usd = parseFloat(headers.get('x-venice-balance-usd') ?? '');
    
    const currentBalance = this.store.getState().balance;
    
    if (!isNaN(diem)) {
      // Calculate consumption rate (if we have previous balance)
      let consumptionRate = currentBalance.consumptionRate;
      if (currentBalance.venice.lastUpdated && currentBalance.venice.diem > diem) {
        const timeDiff = Date.now() - currentBalance.venice.lastUpdated.getTime();
        const diemDiff = currentBalance.venice.diem - diem;
        const hoursDiff = timeDiff / (1000 * 60 * 60);
        if (hoursDiff > 0) {
          consumptionRate = diemDiff / hoursDiff;
        }
      }
      
      // Calculate time to depletion
      const timeToDepletion = consumptionRate > 0 && diem > 0
        ? (diem / consumptionRate) * 60 * 60 * 1000
        : null;
      
      // Calculate UTC midnight countdown
      const now = new Date();
      const utcMidnight = new Date(Date.UTC(
        now.getUTCFullYear(),
        now.getUTCMonth(),
        now.getUTCDate() + 1,
        0, 0, 0, 0
      ));
      const resetCountdown = utcMidnight.getTime() - now.getTime();
      
      // Update balance in store
      this.store.updateBalance({
        venice: {
          diem,
          usd: isNaN(usd) ? currentBalance.venice.usd : usd,
          effective: diem + (isNaN(usd) ? currentBalance.venice.usd : usd),
          lastUpdated: new Date(),
        },
        consumptionRate,
        timeToDepletion,
        resetCountdown,
        todayUsed: currentBalance.todayStartBalance - diem,
      });
    }
    
    // Rate limit info is now handled by rateLimiter.updateFromResponse()
  }
  
  /**
   * Handle error response
   */
  private async handleError(response: Response): Promise<VeniceApiError> {
    let body: any = {};
    try {
      body = await response.json();
    } catch {
      // Response body is not JSON
    }
    
    return new VeniceApiError(
      response.status,
      body.error?.type ?? 'unknown',
      body.error?.message ?? 'Unknown error',
      body.error?.code
    );
  }
  
  /**
   * Get current balance (from store)
   */
  getBalance(): { diem: number; usd: number; effective: number } {
    const balance = this.store.getState().balance;
    return {
      diem: balance.venice.diem,
      usd: balance.venice.usd,
      effective: balance.venice.effective,
    };
  }
  
  /**
   * Get rate limit state
   */
  getRateLimits() {
    return this.rateLimiter.getState();
  }
  
  /**
   * Get rate limit warning
   */
  getRateLimitWarning() {
    return this.rateLimiter.getWarning();
  }
}
