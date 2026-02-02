/**
 * OpenCode Client
 * Connects to OpenCode via SDK v2 and forwards events to state store
 */
import { StateStore } from '../state/store.js';
import { createOpenCodeClient as createCompleteClient } from './client-complete.js';

/**
 * Create and configure OpenCode client
 * Uses complete implementation with proper error handling and logging
 */
export async function createOpenCodeClient(
  store: StateStore,
  config?: {
    baseUrl?: string;
    directory?: string;
    fetch?: typeof globalThis.fetch;
  }
): Promise<ReturnType<typeof createCompleteClient> extends Promise<infer T> ? T : never> {
  return createCompleteClient(store, config);
}
