/**
 * Unit Tests for State Store
 * Production-grade testing
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { StateStore } from '../../src/state/store.js';

describe('StateStore', () => {
  let store: StateStore;
  
  beforeEach(() => {
    store = new StateStore();
  });
  
  describe('Balance Updates', () => {
    it('updates balance correctly', () => {
      store.updateBalance({
        venice: {
          diem: 42.5,
          usd: 10.0,
          effective: 52.5,
          lastUpdated: new Date(),
        },
      });
      
      const state = store.getState();
      expect(state.balance.venice.diem).toBe(42.5);
      expect(state.balance.venice.usd).toBe(10.0);
      expect(state.balance.venice.effective).toBe(52.5);
    });
    
    it('calculates consumption rate', () => {
      // Set initial balance
      store.updateBalance({
        venice: {
          diem: 50.0,
          usd: 10.0,
          effective: 60.0,
          lastUpdated: new Date(Date.now() - 3600000), // 1 hour ago
        },
      });
      
      // Update with lower balance (consumed 5 Diem in 1 hour)
      store.updateBalance({
        venice: {
          diem: 45.0,
          usd: 10.0,
          effective: 55.0,
          lastUpdated: new Date(),
        },
      });
      
      const state = store.getState();
      expect(state.balance.consumptionRate).toBeGreaterThan(0);
    });
    
    it('calculates alert level correctly', () => {
      // Normal balance
      store.updateBalance({
        venice: { diem: 50.0, usd: 10.0, effective: 60.0, lastUpdated: new Date() },
        timeToDepletion: 8 * 60 * 60 * 1000, // 8 hours
      });
      expect(store.getState().balance.alertLevel).toBe('normal');
      
      // Warning balance
      store.updateBalance({
        venice: { diem: 10.0, usd: 10.0, effective: 20.0, lastUpdated: new Date() },
        timeToDepletion: 2 * 60 * 60 * 1000, // 2 hours
      });
      expect(store.getState().balance.alertLevel).toBe('warning');
      
      // Critical balance
      store.updateBalance({
        venice: { diem: 1.0, usd: 0.0, effective: 1.0, lastUpdated: new Date() },
        timeToDepletion: 30 * 60 * 1000, // 30 minutes
      });
      expect(store.getState().balance.alertLevel).toBe('critical');
    });
  });
  
  describe('Session Updates', () => {
    it('creates new session', () => {
      store.updateSession({
        id: 'sess_123',
        promptTokens: 1000,
        completionTokens: 500,
        totalTokens: 1500,
        cost: 0.001,
        model: 'llama-3.3-70b',
        provider: 'venice',
        messageCount: 1,
        startedAt: new Date(),
        updatedAt: new Date(),
      });
      
      const state = store.getState();
      expect(state.session).not.toBeNull();
      expect(state.session?.id).toBe('sess_123');
      expect(state.session?.promptTokens).toBe(1000);
    });
    
    it('updates existing session', () => {
      store.updateSession({
        id: 'sess_123',
        promptTokens: 1000,
        completionTokens: 500,
        totalTokens: 1500,
        cost: 0.001,
        model: 'llama-3.3-70b',
        provider: 'venice',
        messageCount: 1,
        startedAt: new Date(),
        updatedAt: new Date(),
      });
      
      store.updateSession({
        promptTokens: 2000,
        completionTokens: 1000,
      });
      
      const state = store.getState();
      expect(state.session?.promptTokens).toBe(2000);
      expect(state.session?.completionTokens).toBe(1000);
    });
    
    it('clears session', () => {
      store.updateSession({
        id: 'sess_123',
        promptTokens: 1000,
        completionTokens: 500,
        totalTokens: 1500,
        cost: 0.001,
        model: 'llama-3.3-70b',
        provider: 'venice',
        messageCount: 1,
        startedAt: new Date(),
        updatedAt: new Date(),
      });
      
      store.clearSession();
      
      const state = store.getState();
      expect(state.session).toBeNull();
    });
  });
  
  describe('Event Emission', () => {
    it('emits change events on balance update', (done) => {
      store.onStateChange((path, value) => {
        if (path === 'balance') {
          expect(value).toBeDefined();
          done();
        }
      });
      
      store.updateBalance({
        venice: {
          diem: 42.5,
          usd: 10.0,
          effective: 52.5,
          lastUpdated: new Date(),
        },
      });
    });
    
    it('emits change events on session update', (done) => {
      store.onStateChange((path, value) => {
        if (path === 'session') {
          expect(value).toBeDefined();
          done();
        }
      });
      
      store.updateSession({
        id: 'sess_123',
        promptTokens: 1000,
        completionTokens: 500,
        totalTokens: 1500,
        cost: 0.001,
        model: 'llama-3.3-70b',
        provider: 'venice',
        messageCount: 1,
        startedAt: new Date(),
        updatedAt: new Date(),
      });
    });
  });
});
