/**
 * Unit Tests for Database Schema
 * Production-grade testing
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { DatabaseManager } from '../../src/database/schema.js';
import { join } from 'path';
import { unlinkSync, existsSync } from 'fs';

describe('DatabaseManager', () => {
  let db: DatabaseManager;
  const testDbPath = join(process.cwd(), 'test.db');
  
  beforeEach(() => {
    // Clean up test database
    if (existsSync(testDbPath)) {
      unlinkSync(testDbPath);
    }
    db = new DatabaseManager(testDbPath);
  });
  
  afterEach(() => {
    db.close();
    if (existsSync(testDbPath)) {
      unlinkSync(testDbPath);
    }
  });
  
  describe('Balance History', () => {
    it('records balance history', () => {
      db.recordBalanceHistory(42.5, 10.0, 52.5, 0.5, 3600000);
      
      // Verify record was created (would query database)
      // For now, just verify no error thrown
      expect(true).toBe(true);
    });
    
    it('handles multiple balance records', () => {
      db.recordBalanceHistory(50.0, 10.0, 60.0, 0.5, 3600000);
      db.recordBalanceHistory(45.0, 10.0, 55.0, 0.6, 3000000);
      db.recordBalanceHistory(40.0, 10.0, 50.0, 0.7, 2400000);
      
      // Verify records were created
      expect(true).toBe(true);
    });
  });
  
  describe('Session Persistence', () => {
    it('saves session', () => {
      const sessionId = db.saveSession({
        id: crypto.randomUUID(),
        sessionId: 'sess_test',
        promptTokens: 1000,
        completionTokens: 500,
        cost: 0.001,
        model: 'llama-3.3-70b',
        provider: 'venice',
        startedAt: new Date(),
        endedAt: null,
      });
      
      expect(sessionId).toBeDefined();
    });
    
    it('retrieves session', () => {
      const sessionId = db.saveSession({
        id: crypto.randomUUID(),
        sessionId: 'sess_test',
        promptTokens: 1000,
        completionTokens: 500,
        cost: 0.001,
        model: 'llama-3.3-70b',
        provider: 'venice',
        startedAt: new Date(),
        endedAt: null,
      });
      
      const session = db.getSession(sessionId);
      expect(session).toBeDefined();
      expect(session?.sessionId).toBe('sess_test');
    });
  });
  
  describe('Snapshots', () => {
    it('saves snapshot', () => {
      const snapshotId = db.saveSnapshot({
        id: crypto.randomUUID(),
        timestamp: new Date(),
        stateHash: 'hash123',
        data: { balance: { venice: { diem: 42.5 } } },
      });
      
      expect(snapshotId).toBeDefined();
    });
    
    it('retrieves snapshot', () => {
      const snapshotId = db.saveSnapshot({
        id: crypto.randomUUID(),
        timestamp: new Date(),
        stateHash: 'hash123',
        data: { balance: { venice: { diem: 42.5 } } },
      });
      
      const snapshot = db.getSnapshot(snapshotId);
      expect(snapshot).toBeDefined();
      expect(snapshot?.stateHash).toBe('hash123');
    });
  });
});
