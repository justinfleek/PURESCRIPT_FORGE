import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { createStore } from 'solid-js/store';
import { persisted, Persist } from '@/utils/persist';

// Mock platform
vi.mock('@/context/platform', () => ({
  usePlatform: () => ({ platform: 'web' }),
}));

describe('persist utilities', () => {
  beforeEach(() => {
    localStorage.clear();
  });

  afterEach(() => {
    localStorage.clear();
  });

  it('persists and restores store', async () => {
    const [store, setStore] = createStore({ count: 0 });
    const [persistedStore, setPersistedStore] = persisted(
      Persist.global('test-key'),
      [store, setStore]
    );

    setPersistedStore('count', 42);

    // Create new store instance - should restore
    const [store2, setStore2] = createStore({ count: 0 });
    const [persistedStore2] = persisted(
      Persist.global('test-key'),
      [store2, setStore2]
    );

    await new Promise(resolve => setTimeout(resolve, 100));
    expect(persistedStore2.count).toBe(42);
  });

  it('handles quota exceeded gracefully', () => {
    // Mock quota exceeded
    const originalSetItem = localStorage.setItem;
    localStorage.setItem = vi.fn(() => {
      throw new DOMException('QuotaExceededError', 'QuotaExceededError');
    });

    const [store, setStore] = createStore({ data: 'x'.repeat(1000000) });
    const [persistedStore] = persisted(
      Persist.global('large-key'),
      [store, setStore]
    );

    // Should not throw
    expect(persistedStore).toBeDefined();

    localStorage.setItem = originalSetItem;
  });
});
