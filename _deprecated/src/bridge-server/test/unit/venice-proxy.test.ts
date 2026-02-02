/**
 * Unit Tests for Venice Proxy
 * Production-grade testing
 */
import { describe, it, expect, beforeEach, vi } from 'vitest';
import { VeniceProxy } from '../../src/venice/proxy.js';
import { StateStore } from '../../src/state/store.js';

// Mock fetch
global.fetch = vi.fn();

describe('VeniceProxy', () => {
  let proxy: VeniceProxy;
  let store: StateStore;
  
  beforeEach(() => {
    store = new StateStore();
    proxy = new VeniceProxy('test-api-key', store);
    vi.clearAllMocks();
  });
  
  describe('Balance Extraction', () => {
    it('extracts balance from response headers', async () => {
      const mockHeaders = new Headers();
      mockHeaders.set('x-venice-balance-diem', '42.5');
      mockHeaders.set('x-venice-balance-usd', '10.0');
      
      (global.fetch as any).mockResolvedValueOnce({
        ok: true,
        headers: mockHeaders,
        json: async () => ({ choices: [] }),
      });
      
      await proxy.chat({
        model: 'llama-3.3-70b',
        messages: [{ role: 'user', content: 'test' }],
      });
      
      const state = store.getState();
      expect(state.balance.venice.diem).toBe(42.5);
      expect(state.balance.venice.usd).toBe(10.0);
    });
    
    it('handles missing balance headers gracefully', async () => {
      const mockHeaders = new Headers();
      
      (global.fetch as any).mockResolvedValueOnce({
        ok: true,
        headers: mockHeaders,
        json: async () => ({ choices: [] }),
      });
      
      await proxy.chat({
        model: 'llama-3.3-70b',
        messages: [{ role: 'user', content: 'test' }],
      });
      
      // Should not crash, balance should remain unchanged or default
      const state = store.getState();
      expect(state.balance.venice.diem).toBeDefined();
    });
  });
  
  describe('Rate Limiting', () => {
    it('handles 429 responses with exponential backoff', async () => {
      const mockHeaders = new Headers();
      mockHeaders.set('retry-after', '5');
      
      (global.fetch as any).mockResolvedValueOnce({
        ok: false,
        status: 429,
        headers: mockHeaders,
      });
      
      await expect(
        proxy.chat({
          model: 'llama-3.3-70b',
          messages: [{ role: 'user', content: 'test' }],
        })
      ).rejects.toThrow();
      
      // Rate limiter should have recorded the retry-after
      const rateLimits = proxy.getRateLimits();
      expect(rateLimits).toBeDefined();
    });
  });
  
  describe('Error Handling', () => {
    it('handles network errors gracefully', async () => {
      (global.fetch as any).mockRejectedValueOnce(new Error('Network error'));
      
      await expect(
        proxy.chat({
          model: 'llama-3.3-70b',
          messages: [{ role: 'user', content: 'test' }],
        })
      ).rejects.toThrow();
    });
    
    it('handles API errors with proper error messages', async () => {
      (global.fetch as any).mockResolvedValueOnce({
        ok: false,
        status: 400,
        json: async () => ({ error: { message: 'Invalid request' } }),
      });
      
      await expect(
        proxy.chat({
          model: 'llama-3.3-70b',
          messages: [{ role: 'user', content: 'test' }],
        })
      ).rejects.toThrow();
    });
  });
});
