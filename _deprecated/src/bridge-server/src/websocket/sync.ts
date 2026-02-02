/**
 * State Synchronization Logic
 * Delta sync, conflict resolution, optimistic updates
 */
import { StateStore, AppState } from '../state/store.js';

export interface DeltaUpdate {
  path: string;
  value: any;
  timestamp: string;
}

export interface SyncRequest {
  since?: string; // ISO timestamp of last sync
}

export interface SyncResponse {
  type: 'full' | 'delta';
  state?: AppState;
  changes?: DeltaUpdate[];
  timestamp: string;
}

/**
 * State Synchronization Manager
 */
export class StateSyncManager {
  private store: StateStore;
  private changeHistory: DeltaUpdate[] = [];
  private maxHistorySize = 1000;
  private unsubscribe: (() => void) | null = null;
  
  constructor(store: StateStore) {
    this.store = store;
    
    // Track all state changes
    this.unsubscribe = store.onStateChange((path, value) => {
      this.recordChange(path, value);
    });
  }
  
  /**
   * Cleanup
   */
  destroy(): void {
    if (this.unsubscribe) {
      this.unsubscribe();
      this.unsubscribe = null;
    }
  }
  
  /**
   * Get state sync (full or delta)
   */
  getSync(request: SyncRequest): SyncResponse {
    const state = this.store.getState();
    
    if (!request.since) {
      // Full sync
      return {
        type: 'full',
        state,
        timestamp: new Date().toISOString(),
      };
    }
    
    // Delta sync - get changes since timestamp
    const since = new Date(request.since);
    const changes = this.changeHistory.filter(
      change => new Date(change.timestamp) > since
    );
    
    // If too many changes, return full state
    if (changes.length > 100) {
      return {
        type: 'full',
        state,
        timestamp: new Date().toISOString(),
      };
    }
    
    return {
      type: 'delta',
      changes,
      timestamp: new Date().toISOString(),
    };
  }
  
  /**
   * Record state change
   */
  private recordChange(path: string, value: any): void {
    this.changeHistory.push({
      path,
      value,
      timestamp: new Date().toISOString(),
    });
    
    // Trim history if too large
    if (this.changeHistory.length > this.maxHistorySize) {
      this.changeHistory = this.changeHistory.slice(-this.maxHistorySize);
    }
  }
  
  /**
   * Apply delta updates to state
   */
  applyDelta(changes: DeltaUpdate[]): void {
    for (const change of changes) {
      const [category, ...rest] = change.path.split('.');
      
      switch (category) {
        case 'balance':
          this.store.updateBalance(change.value);
          break;
        case 'session':
          if (change.value === null) {
            this.store.clearSession();
          } else {
            this.store.updateSession(change.value);
          }
          break;
        case 'proof':
          this.store.updateProof(change.value);
          break;
        case 'metrics':
          this.store.updateMetrics(change.value);
          break;
        case 'connected':
          this.store.setConnected(change.value);
          break;
        default:
          console.warn('Unknown state path:', change.path);
      }
    }
  }
}
