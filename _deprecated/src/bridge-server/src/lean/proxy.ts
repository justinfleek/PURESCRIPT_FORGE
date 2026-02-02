/**
 * Lean Proxy
 * Forwards Lean4 LSP requests via MCP and updates state store
 */
import { StateStore } from '../state/store.js';
import { LeanMCPClient, LeanGoal, LeanDiagnostic, LeanCompletion } from './mcp-client.js';

/**
 * Lean Proxy - Manages Lean4 LSP connection and requests
 */
export class LeanProxy {
  private mcp: LeanMCPClient;
  private store: StateStore;
  private debounceTimers: Map<string, NodeJS.Timeout> = new Map();
  
  constructor(store: StateStore) {
    this.store = store;
    this.mcp = new LeanMCPClient(store);
  }
  
  /**
   * Connect to Lean LSP
   */
  async connect(command: string, args: string[]): Promise<void> {
    try {
      await this.mcp.connect(command, args);
      this.store.updateProof({ connected: true });
    } catch (error) {
      console.error('Lean LSP connection failed:', error);
      this.store.updateProof({ connected: false });
      // Continue without Lean features
    }
  }
  
  /**
   * Get goals at position (with debouncing for file edits)
   */
  async getGoals(file: string, line: number, column: number): Promise<LeanGoal[]> {
    if (!this.mcp.isConnected()) {
      return [];
    }
    
    // Debounce rapid requests
    const key = `${file}:${line}:${column}`;
    const existing = this.debounceTimers.get(key);
    if (existing) {
      clearTimeout(existing);
    }
    
    return new Promise((resolve) => {
      const timer = setTimeout(async () => {
        this.debounceTimers.delete(key);
        try {
          const goals = await this.mcp.getGoals(file, line, column);
          resolve(goals);
        } catch (error) {
          console.error('Failed to get Lean goals:', error);
          resolve([]);
        }
      }, 300); // 300ms debounce
      
      this.debounceTimers.set(key, timer);
    });
  }
  
  /**
   * Get diagnostics for file
   */
  async getDiagnostics(file: string): Promise<LeanDiagnostic[]> {
    if (!this.mcp.isConnected()) {
      return [];
    }
    
    try {
      return await this.mcp.getDiagnostics(file);
    } catch (error) {
      console.error('Failed to get Lean diagnostics:', error);
      return [];
    }
  }
  
  /**
   * Get completions at position
   */
  async getCompletions(file: string, line: number, column: number): Promise<LeanCompletion[]> {
    if (!this.mcp.isConnected()) {
      return [];
    }
    
    try {
      return await this.mcp.getCompletions(file, line, column);
    } catch (error) {
      console.error('Failed to get Lean completions:', error);
      return [];
    }
  }
  
  /**
   * Check Lean file (get goals + diagnostics)
   */
  async checkFile(file: string, line: number, column: number): Promise<{
    goals: LeanGoal[];
    diagnostics: LeanDiagnostic[];
  }> {
    const [goals, diagnostics] = await Promise.all([
      this.getGoals(file, line, column),
      this.getDiagnostics(file),
    ]);
    
    return { goals, diagnostics };
  }
  
  /**
   * Disconnect from Lean LSP
   */
  async disconnect(): Promise<void> {
    // Clear all debounce timers
    for (const timer of this.debounceTimers.values()) {
      clearTimeout(timer);
    }
    this.debounceTimers.clear();
    
    await this.mcp.disconnect();
  }
}
