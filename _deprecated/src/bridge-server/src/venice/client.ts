/**
 * Complete Venice API Client
 * 
 * Full implementation of Venice API including:
 * - Chat completions (streaming and non-streaming)
 * - Model listing
 * - Image generation
 * - Balance extraction from headers
 * 
 * Spec: 10-VENICE-API-OVERVIEW
 */
import { StateStore } from '../state/store.js';
import { RateLimiter } from './rate-limiter.js';
import { VeniceApiError } from './proxy.js';
import pino from 'pino';

const logger = pino({ name: 'venice-client' });

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

export interface ChatChunk {
  id: string;
  object: 'chat.completion.chunk';
  created: number;
  model: string;
  choices: Array<{
    index: number;
    delta: {
      role?: string;
      content?: string;
    };
    finish_reason?: 'stop' | 'length' | 'content_filter';
  }>;
}

export interface Model {
  id: string;
  object: 'model';
  created: number;
  owned_by: string;
  pricing: {
    input: number; // $ per 1M tokens
    output: number; // $ per 1M tokens
  };
  tier: 'XS' | 'S' | 'M' | 'L';
  context_length: number;
}

export interface ModelsResponse {
  object: 'list';
  data: Model[];
}

export interface ImageGenerationRequest {
  model: string;
  prompt: string;
  width?: number;
  height?: number;
  seed?: number;
  hide_watermark?: boolean;
  return_binary?: boolean;
}

export interface ImageGenerationResponse {
  images: string[]; // Base64 encoded or URLs
  request: {
    width: number;
    height: number;
    seed: number;
    model: string;
    prompt: string;
  };
}

/**
 * Complete Venice API Client
 */
export class VeniceClient {
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
   * Chat completion (non-streaming)
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
      body: JSON.stringify({ ...request, stream: false }),
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
   * Chat completion (streaming)
   * Returns async iterable of chunks
   */
  async *chatStream(request: ChatCompletionRequest): AsyncIterable<ChatChunk> {
    // Acquire rate limit
    await this.rateLimiter.acquire();
    
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ ...request, stream: true }),
    });
    
    // Extract balance from headers (even on streaming)
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
    
    // Parse SSE stream
    const reader = response.body?.getReader();
    if (!reader) {
      throw new Error('Response body is not readable');
    }
    
    const decoder = new TextDecoder();
    let buffer = '';
    
    try {
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        
        buffer += decoder.decode(value, { stream: true });
        const lines = buffer.split('\n');
        buffer = lines.pop() ?? '';
        
        for (const line of lines) {
          if (line.startsWith('data: ')) {
            const data = line.slice(6).trim();
            if (data === '[DONE]') {
              return;
            }
            
            try {
              const chunk = JSON.parse(data) as ChatChunk;
              yield chunk;
            } catch (error) {
              logger.warn('Failed to parse SSE chunk', { error, data });
            }
          }
        }
      }
    } finally {
      reader.releaseLock();
    }
  }
  
  /**
   * List available models
   */
  async listModels(): Promise<Model[]> {
    const response = await fetch(`${this.baseUrl}/models`, {
      method: 'GET',
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
      },
    });
    
    // Extract balance from headers
    this.extractAndUpdateBalance(response.headers);
    
    // Update rate limiter
    this.rateLimiter.updateFromResponse(response.headers);
    
    if (!response.ok) {
      throw await this.handleError(response);
    }
    
    const result = await response.json() as ModelsResponse;
    return result.data;
  }
  
  /**
   * Generate images
   */
  async generateImage(request: ImageGenerationRequest): Promise<ImageGenerationResponse> {
    // Acquire rate limit
    await this.rateLimiter.acquire();
    
    const response = await fetch(`${this.baseUrl}/images/generations`, {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        model: request.model,
        prompt: request.prompt,
        width: request.width ?? 1024,
        height: request.height ?? 1024,
        seed: request.seed,
        hide_watermark: request.hide_watermark ?? false,
        return_binary: request.return_binary ?? false,
      }),
    });
    
    // Extract balance from headers
    this.extractAndUpdateBalance(response.headers);
    
    // Update rate limiter
    this.rateLimiter.updateFromResponse(response.headers);
    
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
  }
  
  /**
   * Handle error response
   */
  private async handleError(response: Response): Promise<VeniceApiError> {
    let body: Record<string, unknown> = {};
    try {
      body = await response.json() as Record<string, unknown>;
    } catch {
      // Response body is not JSON
    }
    
    const error = body.error as { type?: string; message?: string; code?: string } | undefined;
    
    return new VeniceApiError(
      response.status,
      error?.type ?? 'unknown',
      error?.message ?? 'Unknown error',
      error?.code
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
