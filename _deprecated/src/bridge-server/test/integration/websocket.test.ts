/**
 * Integration Tests for WebSocket Communication
 * Production-grade integration testing
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { WebSocket } from 'ws';
import { createServer } from 'http';
import { StateStore } from '../../src/state/store.js';
import { WebSocketManager } from '../../src/websocket/manager.js';

describe('WebSocket Integration', () => {
  let server: ReturnType<typeof createServer>;
  let wsManager: WebSocketManager;
  let store: StateStore;
  let port: number;
  
  beforeEach(async () => {
    store = new StateStore();
    server = createServer();
    wsManager = new WebSocketManager(server, store);
    
    // Start server on random port
    await new Promise<void>((resolve) => {
      server.listen(0, () => {
        const address = server.address();
        port = typeof address === 'string' ? 8765 : address?.port ?? 8765;
        resolve();
      });
    });
  });
  
  afterEach(async () => {
    wsManager.close();
    await new Promise<void>((resolve) => {
      server.close(() => resolve());
    });
  });
  
  it('connects and authenticates', async () => {
    const ws = new WebSocket(`ws://localhost:${port}/ws`);
    
    await new Promise<void>((resolve, reject) => {
      ws.on('open', () => {
        // Send auth
        ws.send(JSON.stringify({
          jsonrpc: '2.0',
          id: 1,
          method: 'auth.request',
          params: { token: 'test-token' },
        }));
      });
      
      ws.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        if (msg.method === 'state.sync') {
          expect(msg.params).toBeDefined();
          resolve();
        }
      });
      
      ws.on('error', reject);
      
      setTimeout(() => reject(new Error('Timeout')), 5000);
    });
    
    ws.close();
  });
  
  it('broadcasts balance updates', async () => {
    const ws = new WebSocket(`ws://localhost:${port}/ws`);
    const messages: any[] = [];
    
    await new Promise<void>((resolve) => {
      ws.on('open', () => {
        ws.send(JSON.stringify({
          jsonrpc: '2.0',
          id: 1,
          method: 'auth.request',
          params: { token: 'test-token' },
        }));
      });
      
      ws.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        messages.push(msg);
        
        // Wait for auth + initial sync
        if (messages.length >= 2) {
          // Update balance
          store.updateBalance({
            venice: {
              diem: 42.5,
              usd: 10.0,
              effective: 52.5,
              lastUpdated: new Date(),
            },
          });
        }
        
        // Check for balance update
        if (msg.method === 'balance.update') {
          expect(msg.params.diem).toBe(42.5);
          resolve();
        }
      });
    });
    
    ws.close();
  });
  
  it('handles state.get request', async () => {
    const ws = new WebSocket(`ws://localhost:${port}/ws`);
    
    // Set up state
    store.updateBalance({
      venice: {
        diem: 42.5,
        usd: 10.0,
        effective: 52.5,
        lastUpdated: new Date(),
      },
    });
    
    const response = await new Promise<any>((resolve, reject) => {
      ws.on('open', () => {
        ws.send(JSON.stringify({
          jsonrpc: '2.0',
          id: 1,
          method: 'auth.request',
          params: { token: 'test-token' },
        }));
      });
      
      ws.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        if (msg.id === 2 && msg.result) {
          resolve(msg.result);
        }
      });
      
      setTimeout(() => {
        ws.send(JSON.stringify({
          jsonrpc: '2.0',
          id: 2,
          method: 'state.get',
          params: {},
        }));
      }, 100);
      
      setTimeout(() => reject(new Error('Timeout')), 5000);
    });
    
    expect(response.balance.venice.diem).toBe(42.5);
    ws.close();
  });
});
