/**
 * Integration Tests for State Synchronization
 * Production-grade integration testing
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { StateStore } from '../../src/state/store.js';
import { StateSyncManager, type SyncRequest } from '../../src/websocket/sync.js';

describe('State Synchronization Integration', () => {
  let store: StateStore;
  let syncManager: StateSyncManager;
  
  beforeEach(() => {
    store = new StateStore();
    syncManager = new StateSyncManager(store);
  });
  
  afterEach(() => {
    // Cleanup
  });
  
  it('provides full sync when no since timestamp', () => {
    // Set up state
    store.updateBalance({
      venice: {
        diem: 42.5,
        usd: 10.0,
        effective: 52.5,
        lastUpdated: new Date(),
      },
    });
    
    const request: SyncRequest = {};
    const sync = syncManager.getSync(request);
    
    expect(sync.type).toBe('full');
    expect(sync.state).toBeDefined();
    expect(sync.state?.balance.venice.diem).toBe(42.5);
  });
  
  it('provides delta sync when since timestamp provided', () => {
    // Set up initial state
    store.updateBalance({
      venice: {
        diem: 50.0,
        usd: 10.0,
        effective: 60.0,
        lastUpdated: new Date(),
      },
    });
    
    const since = new Date().toISOString();
    
    // Make changes
    store.updateBalance({
      venice: {
        diem: 45.0,
        usd: 10.0,
        effective: 55.0,
        lastUpdated: new Date(),
      },
    });
    
    const request: SyncRequest = { since };
    const sync = syncManager.getSync(request);
    
    expect(sync.type).toBe('delta');
    expect(sync.changes).toBeDefined();
    expect(sync.changes?.length).toBeGreaterThan(0);
  });
  
  it('falls back to full sync when too many changes', () => {
    // Set up state
    const since = new Date(Date.now() - 3600000).toISOString();
    
    // Make many changes
    for (let i = 0; i < 150; i++) {
      store.updateBalance({
        venice: {
          diem: 50.0 - i * 0.1,
          usd: 10.0,
          effective: 60.0 - i * 0.1,
          lastUpdated: new Date(),
        },
      });
    }
    
    const request: SyncRequest = { since };
    const sync = syncManager.getSync(request);
    
    expect(sync.type).toBe('full');
    expect(sync.state).toBeDefined();
  });
  
  it('applies delta updates correctly', () => {
    const changes = [
      {
        path: 'balance.venice.diem',
        value: 42.5,
        timestamp: new Date().toISOString(),
      },
      {
        path: 'session',
        value: {
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
        },
        timestamp: new Date().toISOString(),
      },
    ];
    
    syncManager.applyDelta(changes);
    
    const state = store.getState();
    expect(state.balance.venice.diem).toBe(42.5);
    expect(state.session).not.toBeNull();
    expect(state.session?.id).toBe('sess_123');
  });
});
