/**
 * E2E Tests for Bridge Server
 * Production-grade end-to-end testing
 */
import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { WebSocket } from 'ws';
import { createServer } from 'http';
import express from 'express';
import { StateStore } from '../../src/state/store.js';
import { WebSocketManager } from '../../src/websocket/manager.js';
import { VeniceProxy } from '../../src/venice/proxy.js';

describe('Bridge Server E2E', () => {
  let server: ReturnType<typeof createServer>;
  let wsManager: WebSocketManager;
  let store: StateStore;
  let veniceProxy: VeniceProxy | null = null;
  let port: number;
  
  beforeAll(async () => {
    store = new StateStore();
    
    const app = express();
    server = createServer(app);
    wsManager = new WebSocketManager(server, store);
    
    // Create Venice proxy (mock API key for testing)
    if (process.env.VENICE_API_KEY) {
      veniceProxy = new VeniceProxy(process.env.VENICE_API_KEY, store);
    }
    
    await new Promise<void>((resolve) => {
      server.listen(0, () => {
        const address = server.address();
        port = typeof address === 'string' ? 8765 : address?.port ?? 8765;
        resolve();
      });
    });
  });
  
  afterAll(async () => {
    wsManager.close();
    await new Promise<void>((resolve) => {
      server.close(() => resolve());
    });
  });
  
  it('full flow: balance update → broadcast → client receives', async () => {
    const ws = new WebSocket(`ws://localhost:${port}/ws`);
    const receivedMessages: any[] = [];
    
    await new Promise<void>((resolve, reject) => {
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
        receivedMessages.push(msg);
        
        // After auth, trigger balance update
        if (msg.result?.valid && receivedMessages.length === 1) {
          store.updateBalance({
            venice: {
              diem: 42.5,
              usd: 10.0,
              effective: 52.5,
              lastUpdated: new Date(),
            },
          });
        }
        
        // Check for balance update broadcast
        if (msg.method === 'balance.update') {
          expect(msg.params.venice.diem).toBe(42.5);
          expect(msg.params.venice.usd).toBe(10.0);
          expect(msg.params.venice.effective).toBe(52.5);
          resolve();
        }
      });
      
      ws.on('error', reject);
      setTimeout(() => reject(new Error('Timeout')), 10000);
    });
    
    ws.close();
  });
  
  it('full flow: session created → updated → cleared', async () => {
    const ws = new WebSocket(`ws://localhost:${port}/ws`);
    const sessionEvents: any[] = [];
    
    await new Promise<void>((resolve, reject) => {
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
        
        if (msg.method === 'session.update') {
          sessionEvents.push(msg);
        }
        
        // After auth, create session
        if (msg.result?.valid && sessionEvents.length === 0) {
          store.updateSession({
            id: 'sess_e2e_test',
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
        }
        
        // Update session
        if (sessionEvents.length === 1) {
          store.updateSession({
            promptTokens: 2000,
            completionTokens: 1000,
          });
        }
        
        // Clear session
        if (sessionEvents.length === 2) {
          store.clearSession();
        }
        
        // Verify all events received
        if (sessionEvents.length === 3) {
          expect(sessionEvents[0].params.id).toBe('sess_e2e_test');
          expect(sessionEvents[1].params.promptTokens).toBe(2000);
          expect(sessionEvents[2].params).toBeNull();
          resolve();
        }
      });
      
      ws.on('error', reject);
      setTimeout(() => reject(new Error('Timeout')), 10000);
    });
    
    ws.close();
  });
});
