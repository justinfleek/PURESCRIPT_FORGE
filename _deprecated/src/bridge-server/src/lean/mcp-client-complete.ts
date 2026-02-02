/**
 * Lean LSP MCP Client - Complete Implementation
 * Connects to Lean4 LSP via Model Context Protocol
 */
import { MCPClient } from '@modelcontextprotocol/sdk/client/index.js';
import { StateStore } from '../state/store.js';
import pino from 'pino';

const logger = pino({ name: 'lean-mcp-client' });

export interface LeanGoal {
  type: string;
  context: Array<{ name: string; type: string }>;
}

export interface LeanDiagnostic {
  severity: 'error' | 'warning' | 'info';
  message: string;
  range: {
    start: { line: number; col: number };
    end: { line: number; col: number };
  };
}

export interface LeanCompletion {
  text: string;
  type: string;
  documentation?: string;
}

interface MCPToolResult {
  content: Array<{
    type: string;
    text?: string;
    data?: unknown;
  }>;
  isError?: boolean;
}

/**
 * MCP Client for Lean4 LSP
 */
export class LeanMCPClient {
  private client: MCPClient | null = null;
  private store: StateStore;
  private connected: boolean = false;
  
  constructor(store: StateStore) {
    this.store = store;
  }
  
  /**
   * Connect to Lean LSP via MCP
   */
  async connect(command: string, args: string[]): Promise<void> {
    try {
      logger.info('Connecting to Lean LSP via MCP', { command, args });
      
      this.client = new MCPClient({
        name: 'opencode-sidepanel-bridge',
        version: '0.1.0',
      });
      
      await this.client.connect({
        command,
        args,
        transport: {
          type: 'stdio',
        },
      });
      
      // Initialize MCP session
      await this.client.initialize({
        protocolVersion: '2024-11-05',
        capabilities: {},
        clientInfo: {
          name: 'opencode-sidepanel-bridge',
          version: '0.1.0',
        },
      });
      
      this.connected = true;
      this.store.updateProof({ connected: true });
      
      logger.info('Connected to Lean LSP via MCP');
    } catch (error) {
      logger.error('Failed to connect to Lean LSP', {
        error: error instanceof Error ? error.message : String(error),
      });
      this.connected = false;
      this.store.updateProof({ connected: false });
      throw error;
    }
  }
  
  /**
   * Get proof goals at position
   */
  async getGoals(file: string, line: number, column: number): Promise<LeanGoal[]> {
    if (!this.client || !this.connected) {
      throw new Error('Lean LSP not connected');
    }
    
    try {
      logger.debug('Getting Lean goals', { file, line, column });
      
      const result = await this.client.callTool({
        name: 'lean_goal',
        arguments: {
          file,
          line,
          column,
        },
      }) as MCPToolResult;
      
      const goals = this.parseGoals(result);
      
      logger.debug('Parsed Lean goals', { count: goals.length });
      
      this.store.updateProof({
        file,
        position: { line, column },
        goals,
      });
      
      return goals;
    } catch (error) {
      logger.error('Failed to get Lean goals', {
        error: error instanceof Error ? error.message : String(error),
        file,
        line,
        column,
      });
      throw error;
    }
  }
  
  /**
   * Get diagnostics for file
   */
  async getDiagnostics(file: string): Promise<LeanDiagnostic[]> {
    if (!this.client || !this.connected) {
      throw new Error('Lean LSP not connected');
    }
    
    try {
      logger.debug('Getting Lean diagnostics', { file });
      
      const result = await this.client.callTool({
        name: 'lean_diagnostic_messages',
        arguments: { file },
      }) as MCPToolResult;
      
      const diagnostics = this.parseDiagnostics(result);
      
      logger.debug('Parsed Lean diagnostics', { count: diagnostics.length });
      
      this.store.updateProof({
        file,
        diagnostics,
      });
      
      return diagnostics;
    } catch (error) {
      logger.error('Failed to get Lean diagnostics', {
        error: error instanceof Error ? error.message : String(error),
        file,
      });
      throw error;
    }
  }
  
  /**
   * Get completions at position
   */
  async getCompletions(file: string, line: number, column: number): Promise<LeanCompletion[]> {
    if (!this.client || !this.connected) {
      throw new Error('Lean LSP not connected');
    }
    
    try {
      logger.debug('Getting Lean completions', { file, line, column });
      
      const result = await this.client.callTool({
        name: 'lean_completions',
        arguments: {
          file,
          line,
          column,
        },
      }) as MCPToolResult;
      
      const completions = this.parseCompletions(result);
      
      logger.debug('Parsed Lean completions', { count: completions.length });
      
      return completions;
    } catch (error) {
      logger.error('Failed to get Lean completions', {
        error: error instanceof Error ? error.message : String(error),
        file,
        line,
        column,
      });
      throw error;
    }
  }
  
  /**
   * Parse goals from MCP result
   */
  private parseGoals(result: MCPToolResult): LeanGoal[] {
    if (result.isError) {
      logger.warn('MCP tool returned error', { result });
      return [];
    }
    
    if (!result.content || !Array.isArray(result.content)) {
      logger.warn('Invalid MCP result format for goals', { result });
      return [];
    }
    
    const goals: LeanGoal[] = [];
    
    for (const item of result.content) {
      if (item.type === 'text' && item.text) {
        // Parse text format: "goal_type\ncontext_line1\ncontext_line2..."
        const lines = item.text.split('\n');
        if (lines.length > 0) {
          goals.push({
            type: lines[0] ?? '',
            context: lines.slice(1).map((line, index) => ({
              name: `var_${index}`,
              type: line,
            })),
          });
        }
      } else if (item.type === 'object' && item.data) {
        // Parse structured format
        const data = item.data as Record<string, unknown>;
        goals.push({
          type: String(data.type ?? data.goal ?? ''),
          context: Array.isArray(data.context)
            ? (data.context as Array<Record<string, unknown>>).map((ctx) => ({
                name: String(ctx.name ?? ''),
                type: String(ctx.type ?? ''),
              }))
            : [],
        });
      }
    }
    
    return goals;
  }
  
  /**
   * Parse diagnostics from MCP result
   */
  private parseDiagnostics(result: MCPToolResult): LeanDiagnostic[] {
    if (result.isError) {
      logger.warn('MCP tool returned error', { result });
      return [];
    }
    
    if (!result.content || !Array.isArray(result.content)) {
      logger.warn('Invalid MCP result format for diagnostics', { result });
      return [];
    }
    
    const diagnostics: LeanDiagnostic[] = [];
    
    for (const item of result.content) {
      if (item.type === 'object' && item.data) {
        const data = item.data as Record<string, unknown>;
        diagnostics.push({
          severity: (data.severity as 'error' | 'warning' | 'info') ?? 'error',
          message: String(data.message ?? ''),
          range: data.range
            ? (data.range as {
                start: { line: number; character?: number };
                end: { line: number; character?: number };
              })
            : {
                start: { line: 0, col: 0 },
                end: { line: 0, col: 0 },
              },
        });
      }
    }
    
    return diagnostics;
  }
  
  /**
   * Parse completions from MCP result
   */
  private parseCompletions(result: MCPToolResult): LeanCompletion[] {
    if (result.isError) {
      logger.warn('MCP tool returned error', { result });
      return [];
    }
    
    if (!result.content || !Array.isArray(result.content)) {
      logger.warn('Invalid MCP result format for completions', { result });
      return [];
    }
    
    const completions: LeanCompletion[] = [];
    
    for (const item of result.content) {
      if (item.type === 'object' && item.data) {
        const data = item.data as Record<string, unknown>;
        completions.push({
          text: String(data.text ?? data.label ?? ''),
          type: String(data.type ?? data.kind ?? ''),
          documentation: data.documentation ? String(data.documentation) : undefined,
        });
      }
    }
    
    return completions;
  }
  
  /**
   * Disconnect from Lean LSP
   */
  async disconnect(): Promise<void> {
    if (this.client) {
      try {
        logger.info('Disconnecting from Lean LSP');
        await this.client.close();
      } catch (error) {
        logger.error('Error disconnecting from Lean LSP', {
          error: error instanceof Error ? error.message : String(error),
        });
      }
      this.client = null;
    }
    
    this.connected = false;
    this.store.updateProof({ connected: false });
  }
  
  /**
   * Check if connected
   */
  isConnected(): boolean {
    return this.connected;
  }
}
