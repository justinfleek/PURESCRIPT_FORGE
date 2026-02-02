/**
 * WebSocket Manager - Manages browser connections
 * Production-grade WebSocket server with JSON-RPC 2.0
 */
import { WebSocketServer, WebSocket } from 'ws';
import { Server } from 'http';
import { IncomingMessage } from 'http';
import { randomUUID } from 'crypto';
import { StateStore, BalanceState, SessionState, ProofState, UsageMetrics } from '../state/store.js';
import { StateSyncManager, SyncRequest } from './sync.js';
import { DatabaseManager, SessionRecord } from '../database/schema.js';
import * as Handlers from './handlers.js';

export interface JsonRpcRequest {
  jsonrpc: '2.0';
  id?: number | string;
  method: string;
  params?: Record<string, any>;
}

export interface JsonRpcResponse {
  jsonrpc: '2.0';
  id: number | string;
  result?: any;
  error?: JsonRpcError;
}

export interface JsonRpcNotification {
  jsonrpc: '2.0';
  method: string;
  params?: Record<string, any>;
}

export interface JsonRpcError {
  code: number;
  message: string;
  data?: any;
}

interface ClientConnection {
  id: string;
  ws: WebSocket;
  isAuthenticated: boolean;
  lastPing: number;
  connectedAt: Date;
}

/**
 * WebSocket Manager - Handles all WebSocket connections
 */
export class WebSocketManager {
  private wss: WebSocketServer;
  private clients: Map<string, ClientConnection> = new Map();
  private pingInterval: NodeJS.Timeout | null = null;
  private store: StateStore;
  private syncManager: StateSyncManager;
  private handlerContext: Handlers.HandlerContext | null = null;
  
  constructor(server: Server, store: StateStore) {
    this.store = store;
    this.syncManager = new StateSyncManager(store);
    this.wss = new WebSocketServer({ server, path: '/ws' });
    this.wss.on('connection', this.handleConnection.bind(this));
    
    // Start ping interval (30 seconds)
    this.pingInterval = setInterval(() => {
      this.pingAllClients();
    }, 30000);
  }
  
  /**
   * Set handler context (called after services are initialized)
   */
  setHandlerContext(context: Handlers.HandlerContext): void {
    this.handlerContext = context;
  }
  
  /**
   * Handle new WebSocket connection
   */
  private handleConnection(ws: WebSocket, req: IncomingMessage): void {
    const clientId = randomUUID();
    const client: ClientConnection = {
      id: clientId,
      ws,
      isAuthenticated: false,
      lastPing: Date.now(),
      connectedAt: new Date(),
    };
    
    this.clients.set(clientId, client);
    
    // Authentication timeout (5 seconds)
    const authTimeout = setTimeout(() => {
      if (!client.isAuthenticated) {
        this.sendError(ws, null, -32000, 'Authentication timeout');
        ws.close(4002, 'Authentication timeout');
        this.clients.delete(clientId);
      }
    }, 5000);
    
    ws.on('message', async (data: Buffer) => {
      try {
        const msg = JSON.parse(data.toString()) as JsonRpcRequest | JsonRpcNotification;
        
        // Handle authentication
        if ('method' in msg && msg.method === 'auth.request') {
          clearTimeout(authTimeout);
          await this.authenticateClient(client, msg.params);
          return;
        }
        
        // Require authentication for other messages
        if (!client.isAuthenticated) {
          this.sendError(ws, msg.id ?? null, -32000, 'Not authenticated');
          return;
        }
        
        // Handle request (has id)
        if ('id' in msg && msg.id !== undefined) {
          await this.handleRequest(client, msg as JsonRpcRequest);
        } else {
          // Handle notification (no id)
          await this.handleNotification(client, msg as JsonRpcNotification);
        }
      } catch (error) {
        const err = error instanceof Error ? error : new Error(String(error));
        this.sendError(ws, null, -32700, 'Parse error', { error: err.message });
        // Clear timeout on error to prevent memory leak
        clearTimeout(authTimeout);
      }
    });
    
    ws.on('close', () => {
      clearTimeout(authTimeout);
      this.clients.delete(clientId);
    });
    
    ws.on('close', () => {
      clearTimeout(authTimeout);
      this.clients.delete(clientId);
    });
    
    ws.on('error', (error) => {
      console.error(`WebSocket error for client ${clientId}:`, error);
    });
    
    ws.on('pong', () => {
      client.lastPing = Date.now();
    });
  }
  
  /**
   * Authenticate client
   */
  private async authenticateClient(
    client: ClientConnection,
    params: Record<string, any> | undefined
  ): Promise<void> {
    // TODO: Implement proper authentication
    // For now, accept any token (development mode)
    const token = params?.token;
    
    if (!token) {
      this.sendError(client.ws, null, -32602, 'Invalid params: token required');
      return;
    }
    
    client.isAuthenticated = true;
    
    // Send authentication success
    this.sendResponse(client.ws, null, {
      valid: true,
      expires: new Date(Date.now() + 24 * 60 * 60 * 1000).toISOString(),
    });
    
    // Send initial state
    const state = this.store.getState();
    this.sendNotification(client.ws, 'state.sync', {
      connected: state.connected,
      balance: state.balance,
      session: state.session,
      proof: state.proof,
      metrics: state.metrics,
      timestamp: new Date().toISOString(),
    });
  }
  
  /**
   * Handle JSON-RPC request
   */
  private async handleRequest(
    client: ClientConnection,
    request: JsonRpcRequest
  ): Promise<void> {
    try {
      let result: any;
      
      switch (request.method) {
        case 'state.get':
          result = this.handleStateGet(request.params);
          break;
        
        case 'opencode.event':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleOpenCodeEventMessage(this.handlerContext, request.params ?? {});
          break;
        
        case 'venice.chat':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleVeniceChat(this.handlerContext, request.params ?? {});
          break;
        
        case 'venice.models':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleVeniceModels(this.handlerContext, request.params ?? {});
          break;
        
        case 'venice.image':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleVeniceImage(this.handlerContext, request.params ?? {});
          break;
        
        case 'notification.dismiss':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleNotificationDismiss(this.handlerContext, request.params ?? {});
          break;
        
        case 'notification.dismissAll':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleNotificationDismissAll(this.handlerContext, request.params ?? {});
          break;
        
        case 'balance.refresh':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleBalanceRefresh(this.handlerContext, request.params ?? {});
          break;
        
        case 'session.list':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleSessionList(this.handlerContext, request.params ?? {});
          break;
        
        case 'proof.status':
          if (!this.handlerContext) throw new Error('Handler context not initialized');
          result = await Handlers.handleProofStatus(this.handlerContext, request.params ?? {});
          break;
        
        case 'snapshot.restore':
          result = await this.handleSnapshotRestore(request.params);
          break;
        
        case 'snapshot.list':
          result = await this.handleSnapshotList(request.params);
          break;
        
        case 'alerts.configure':
          result = await this.handleAlertsConfigure(request.params);
          break;
        
        case 'session.export':
          result = await this.handleSessionExport(request.params);
          break;
        
        case 'lean.check':
          result = await this.handleLeanCheck(request.params);
          break;
        
        default:
          throw new Error(`Unknown method: ${request.method}`);
      }
      
      this.sendResponse(client.ws, request.id!, result);
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      this.sendError(client.ws, request.id!, -32603, 'Internal error', { error: err.message });
    }
  }
  
  /**
   * Handle JSON-RPC notification
   */
  private async handleNotification(
    client: ClientConnection,
    notification: JsonRpcNotification
  ): Promise<void> {
    // Handle pong response
    if (notification.method === 'pong') {
      client.lastPing = Date.now();
      return;
    }
    
    // Other notifications can be handled here
  }
  
  /**
   * Broadcast message to all authenticated clients
   */
  broadcast(notification: JsonRpcNotification): void {
    const json = JSON.stringify(notification);
    for (const client of this.clients.values()) {
      if (client.isAuthenticated && client.ws.readyState === WebSocket.OPEN) {
        client.ws.send(json);
      }
    }
  }
  
  /**
   * Send response to client
   */
  private sendResponse(ws: WebSocket, id: number | string | null, result: any): void {
    if (id === null) return;
    
    const response: JsonRpcResponse = {
      jsonrpc: '2.0',
      id,
      result,
    };
    ws.send(JSON.stringify(response));
  }
  
  /**
   * Send error to client
   */
  private sendError(
    ws: WebSocket,
    id: number | string | null,
    code: number,
    message: string,
    data?: any
  ): void {
    const response: JsonRpcResponse = {
      jsonrpc: '2.0',
      id: id ?? 0,
      error: {
        code,
        message,
        ...(data && { data }),
      },
    };
    ws.send(JSON.stringify(response));
  }
  
  /**
   * Send notification to client
   */
  private sendNotification(
    ws: WebSocket,
    method: string,
    params?: Record<string, any>
  ): void {
    const notification: JsonRpcNotification = {
      jsonrpc: '2.0',
      method,
      params,
    };
    ws.send(JSON.stringify(notification));
  }
  
  /**
   * Ping all clients
   */
  private pingAllClients(): void {
    const now = Date.now();
    const notification: JsonRpcNotification = {
      jsonrpc: '2.0',
      method: 'ping',
      params: { timestamp: now },
    };
    
    for (const client of this.clients.values()) {
      if (client.isAuthenticated && client.ws.readyState === WebSocket.OPEN) {
        // Check if client is stale (no pong in 60 seconds)
        if (now - client.lastPing > 60000) {
          client.ws.close(4001, 'Stale connection');
          this.clients.delete(client.id);
          continue;
        }
        
        client.ws.send(JSON.stringify(notification));
      }
    }
  }
  
  /**
   * Request handlers
   */
  private handleStateGet(params: Record<string, any> | undefined): any {
    const syncRequest: SyncRequest = {
      since: params?.since,
    };
    
    const sync = this.syncManager.getSync(syncRequest);
    
    if (sync.type === 'full') {
      return {
        type: 'full',
        connected: sync.state!.connected,
        balance: sync.state!.balance,
        session: sync.state!.session,
        proof: sync.state!.proof,
        metrics: sync.state!.metrics,
        timestamp: sync.timestamp,
      };
    } else {
      return {
        type: 'delta',
        changes: sync.changes,
        timestamp: sync.timestamp,
      };
    }
  }
  
  private async handleSnapshotRestore(params: Record<string, any> | undefined): Promise<any> {
    if (!this.handlerContext) {
      throw new Error('Handler context not initialized');
    }
    
    const snapshotId = params?.id;
    if (!snapshotId || typeof snapshotId !== 'string') {
      throw new Error('Snapshot ID required');
    }
    
    // Get snapshot from database
    const snapshot = this.handlerContext.db.getSnapshot(snapshotId);
    if (!snapshot) {
      throw new Error(`Snapshot not found: ${snapshotId}`);
    }
    
    // Restore state from snapshot
    const stateData = snapshot.data as {
      balance?: Partial<BalanceState>;
      session?: SessionState | null;
      proof?: Partial<ProofState>;
      metrics?: Partial<UsageMetrics>;
    };
    
    if (stateData.balance) {
      this.store.updateBalance(stateData.balance);
    }
    
    if (stateData.session !== undefined) {
      if (stateData.session === null) {
        this.store.clearSession();
      } else {
        this.store.updateSession(stateData.session);
      }
    }
    
    if (stateData.proof) {
      this.store.updateProof(stateData.proof);
    }
    
    if (stateData.metrics) {
      this.store.updateMetrics(stateData.metrics);
    }
    
    return {
      success: true,
      snapshotId,
      restoredAt: new Date().toISOString(),
    };
  }
  
  private async handleSnapshotList(params: Record<string, any> | undefined): Promise<any> {
    if (!this.handlerContext) {
      throw new Error('Handler context not initialized');
    }
    
    const limit = params?.limit ?? 100;
    const snapshots = this.handlerContext.db.listSnapshots(limit);
    
    return {
      snapshots: snapshots.map(s => ({
        id: s.id,
        timestamp: s.timestamp.toISOString(),
        stateHash: s.stateHash,
        trigger: s.trigger,
        description: s.description,
      })),
      count: snapshots.length,
    };
  }
  
  private async handleAlertsConfigure(params: Record<string, any> | undefined): Promise<any> {
    // Alert configuration is stored in state store
    // This handler allows clients to configure alert thresholds
    
    const diemWarning = params?.diemWarning;
    const diemCritical = params?.diemCritical;
    
    if (typeof diemWarning === 'number') {
      // Update balance alert thresholds
      const balance = this.store.getState().balance;
      const alertLevel = balance.venice.diem < (diemCritical ?? 5)
        ? 'critical'
        : balance.venice.diem < diemWarning
        ? 'warning'
        : 'normal';
      
      this.store.updateBalance({ alertLevel });
    }
    
    return {
      success: true,
      config: {
        diemWarning: diemWarning ?? 10,
        diemCritical: diemCritical ?? 5,
      },
    };
  }
  
  private async handleSessionExport(params: Record<string, any> | undefined): Promise<any> {
    if (!this.handlerContext) {
      throw new Error('Handler context not initialized');
    }
    
    const sessionId = params?.sessionId;
    const format = params?.format ?? 'json'; // 'json' | 'markdown' | 'text'
    
    const state = this.store.getState();
    let session: SessionRecord | null = null;
    
    if (sessionId) {
      // Get from database (most recent record for this session)
      const sessions = this.handlerContext.db.getSessionsBySessionId(sessionId);
      session = sessions.length > 0 ? sessions[0] : null;
    } else {
      // Use current session from state
      const currentSession = state.session;
      if (currentSession) {
        // Convert SessionState to SessionRecord format
        session = {
          id: randomUUID(),
          sessionId: currentSession.id,
          promptTokens: currentSession.promptTokens,
          completionTokens: currentSession.completionTokens,
          cost: currentSession.cost,
          model: currentSession.model,
          provider: currentSession.provider,
          startedAt: currentSession.startedAt,
          endedAt: null,
        };
      }
    }
    
    if (!session) {
      throw new Error('Session not found');
    }
    
    // Generate export data
    const exportData = {
      session: {
        id: session.sessionId,
        model: session.model,
        provider: session.provider,
        promptTokens: session.promptTokens,
        completionTokens: session.completionTokens,
        totalTokens: session.promptTokens + session.completionTokens,
        cost: session.cost,
        startedAt: session.startedAt.toISOString(),
        endedAt: session.endedAt?.toISOString() ?? null,
      },
      exportedAt: new Date().toISOString(),
      version: '1.0',
    };
    
    // Format export based on requested format
    let content: string;
    let filename: string;
    let mimeType: string;
    
    switch (format) {
      case 'markdown':
        content = `# Session Export: ${session.sessionId}\n\n` +
          `**Model:** ${session.model}\n` +
          `**Provider:** ${session.provider}\n` +
          `**Tokens:** ${session.promptTokens + session.completionTokens} (${session.promptTokens} prompt + ${session.completionTokens} completion)\n` +
          `**Cost:** $${session.cost.toFixed(4)}\n` +
          `**Started:** ${session.startedAt.toISOString()}\n` +
          (session.endedAt ? `**Ended:** ${session.endedAt.toISOString()}\n` : '');
        filename = `session-${session.sessionId}.md`;
        mimeType = 'text/markdown';
        break;
      
      case 'text':
        content = `Session Export: ${session.sessionId}\n` +
          `Model: ${session.model}\n` +
          `Provider: ${session.provider}\n` +
          `Tokens: ${session.promptTokens + session.completionTokens} (${session.promptTokens} prompt + ${session.completionTokens} completion)\n` +
          `Cost: $${session.cost.toFixed(4)}\n` +
          `Started: ${session.startedAt.toISOString()}\n` +
          (session.endedAt ? `Ended: ${session.endedAt.toISOString()}\n` : '');
        filename = `session-${session.sessionId}.txt`;
        mimeType = 'text/plain';
        break;
      
      case 'json':
      default:
        content = JSON.stringify(exportData, null, 2);
        filename = `session-${session.sessionId}.json`;
        mimeType = 'application/json';
        break;
    }
    
    // Notify about export
    if (this.handlerContext.notificationService) {
      this.handlerContext.notificationService.notifySessionExported(filename);
    }
    
    return {
      success: true,
      filename,
      content,
      mimeType,
      size: content.length,
    };
  }
  
  private async handleLeanCheck(params: Record<string, any> | undefined): Promise<any> {
    if (!this.handlerContext || !this.handlerContext.leanProxy) {
      throw new Error('Lean proxy not available');
    }
    
    const file = params?.file;
    const line = params?.line ?? 0;
    const column = params?.column ?? 0;
    
    if (!file || typeof file !== 'string') {
      throw new Error('File path required');
    }
    
    // Check file with Lean proxy
    const result = await this.handlerContext.leanProxy.checkFile(
      file,
      typeof line === 'number' ? line : parseInt(String(line), 10),
      typeof column === 'number' ? column : parseInt(String(column), 10)
    );
    
    // Update state store with results
    this.store.updateProof({
      file,
      position: { line, column },
      goals: result.goals.map(g => ({
        type: g.type ?? 'unknown',
        context: g.context ?? [],
      })),
      diagnostics: result.diagnostics.map(d => ({
        severity: (d.severity ?? 'info') as 'error' | 'warning' | 'info',
        message: d.message ?? '',
        range: {
          start: { line: d.range?.start?.line ?? 0, col: d.range?.start?.character ?? 0 },
          end: { line: d.range?.end?.line ?? 0, col: d.range?.end?.character ?? 0 },
        },
      })),
    });
    
    return {
      success: true,
      file,
      goals: result.goals,
      diagnostics: result.diagnostics,
      timestamp: new Date().toISOString(),
    };
  }
  
  /**
   * Get connection count
   */
  getConnectionCount(): number {
    return this.clients.size;
  }
  
  /**
   * Close all connections and cleanup
   */
  close(): void {
    if (this.pingInterval) {
      clearInterval(this.pingInterval);
    }
    
    for (const client of this.clients.values()) {
      client.ws.close(1001, 'Server shutting down');
    }
    
    this.clients.clear();
    this.wss.close();
  }
}
