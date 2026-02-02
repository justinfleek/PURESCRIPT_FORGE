/**
 * Unit Tests for Rate Limiter
 * Production-grade testing
 */
import { describe, it, expect, beforeEach, vi } from 'vitest';
import { RateLimiter } from '../../src/venice/rate-limiter.js';

describe('RateLimiter', () => {
  let limiter: RateLimiter;
  
  beforeEach(() => {
    limiter = new RateLimiter();
  });
  
  describe('Rate Limit State', () => {
    it('updates from response headers', () => {
      const headers = new Headers();
      headers.set('x-ratelimit-remaining-requests', '10');
      headers.set('x-ratelimit-limit-requests', '100');
      headers.set('x-ratelimit-reset-requests', new Date(Date.now() + 3600000).toISOString());
      
      limiter.updateFromResponse(headers);
      
      const state = limiter.getState();
      expect(state.requests.remaining).toBe(10);
      expect(state.requests.limit).toBe(100);
    });
    
    it('handles missing headers gracefully', () => {
      const headers = new Headers();
      
      limiter.updateFromResponse(headers);
      
      // Should not crash
      const state = limiter.getState();
      expect(state).toBeDefined();
    });
  });
  
  describe('429 Handling', () => {
    it('records retry-after time', () => {
      limiter.handleRateLimit(5); // 5 seconds
      
      expect(limiter.canProceed('M')).toBe(false);
    });
    
    it('allows requests after retry-after expires', async () => {
      limiter.handleRateLimit(1); // 1 second
      
      expect(limiter.canProceed('M')).toBe(false);
      
      // Wait for retry-after to expire
      await new Promise(resolve => setTimeout(resolve, 1100));
      
      expect(limiter.canProceed('M')).toBe(true);
    });
  });
  
  describe('Warning System', () => {
    it('returns warning when approaching limits', () => {
      const headers = new Headers();
      headers.set('x-ratelimit-remaining-requests', '5');
      headers.set('x-ratelimit-limit-requests', '100');
      headers.set('x-ratelimit-remaining-tokens', '1000');
      headers.set('x-ratelimit-limit-tokens', '100000');
      
      limiter.updateFromResponse(headers);
      
      const warning = limiter.getWarning();
      expect(warning).not.toBeNull();
      expect(warning?.severity).toBe('warning');
    });
    
    it('returns critical warning when very low', () => {
      const headers = new Headers();
      headers.set('x-ratelimit-remaining-requests', '1');
      headers.set('x-ratelimit-limit-requests', '100');
      headers.set('x-ratelimit-remaining-tokens', '100');
      headers.set('x-ratelimit-limit-tokens', '100000');
      
      limiter.updateFromResponse(headers);
      
      const warning = limiter.getWarning();
      expect(warning).not.toBeNull();
      expect(warning?.severity).toBe('critical');
    });
    
    it('returns null when limits are healthy', () => {
      const headers = new Headers();
      headers.set('x-ratelimit-remaining-requests', '80');
      headers.set('x-ratelimit-limit-requests', '100');
      headers.set('x-ratelimit-remaining-tokens', '80000');
      headers.set('x-ratelimit-limit-tokens', '100000');
      
      limiter.updateFromResponse(headers);
      
      const warning = limiter.getWarning();
      expect(warning).toBeNull();
    });
  });
  
  describe('Acquire Rate Limit', () => {
    it('waits when rate limited', async () => {
      limiter.handleRateLimit(1); // 1 second
      
      const start = Date.now();
      await limiter.acquire();
      const elapsed = Date.now() - start;
      
      expect(elapsed).toBeGreaterThanOrEqual(900); // At least 900ms
    });
    
    it('proceeds immediately when not rate limited', async () => {
      const headers = new Headers();
      headers.set('x-ratelimit-remaining-requests', '10');
      headers.set('x-ratelimit-limit-requests', '100');
      
      limiter.updateFromResponse(headers);
      
      const start = Date.now();
      await limiter.acquire();
      const elapsed = Date.now() - start;
      
      expect(elapsed).toBeLessThan(100); // Should be immediate
    });
  });
});
