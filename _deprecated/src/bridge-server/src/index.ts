/**
 * Bridge Server Entry Point
 * Production-grade bridge server connecting OpenCode, Venice API, Lean LSP, and browser
 */
import { createServer } from 'http';
import express from 'express';
import { loadConfig } from './config.js';
import { StateStore } from './state/store.js';
import { WebSocketManager } from './websocket/manager.js';
import { VeniceProxy } from './venice/proxy.js';
import { VeniceClient } from './venice/client.js';
import { LeanProxy } from './lean/proxy.js';
import { createOpenCodeClient } from './opencode/client.js';
import { DatabaseManager } from './database/schema.js';
import { wirePersistence } from './database/persistence.js';
import { NotificationService } from './notifications/service.js';
import { VoiceService } from './voice/integration.js';
import { createVoiceRoutes } from './voice/routes.js';
import pino from 'pino';

const logger = pino({
  level: process.env.LOG_LEVEL ?? 'info',
  transport: process.env.LOG_FORMAT === 'pretty' ? {
    target: 'pino-pretty',
  } : undefined,
});

async function main() {
  const config = loadConfig();
  
  logger.info('Starting Bridge Server', {
    port: config.port,
    host: config.host,
  });
  
  // Create state store
  const store = new StateStore();
  
  // Create HTTP server
  const app = express();
  
  // Health check endpoint
  app.get('/health', (req, res) => {
    res.json({
      status: 'ok',
      uptime: process.uptime(),
      timestamp: new Date().toISOString(),
    });
  });
  
  // Initialize voice service
  let voiceService: VoiceService | null = null;
  if (config.venice.apiKey) {
    try {
      voiceService = new VoiceService({
        veniceApiKey: config.venice.apiKey,
        dbPath: config.storage.path,
        port: 8001,
      });
      await voiceService.start();
      
      // Add voice routes
      const voiceRoutes = createVoiceRoutes(voiceService);
      app.use('/api/voice', voiceRoutes);
      
      logger.info('Voice engine integrated');
    } catch (error) {
      logger.warn('Voice engine failed to start, continuing without voice features:', error);
    }
  } else {
    logger.warn('Venice API key not provided, voice features disabled');
  }
  
  // Static files (frontend bundle)
  app.use(express.static(config.staticDir));
  
  // SPA fallback
  app.get('*', (req, res) => {
    res.sendFile('index.html', { root: config.staticDir });
  });
  
  const server = createServer(app);
  
  // Create WebSocket manager
  const wsManager = new WebSocketManager(server, store);
  
  // Create notification service
  const notificationService = new NotificationService(wsManager);
  
  // Subscribe to state changes and broadcast to clients
  store.onStateChange((path, value) => {
    wsManager.broadcast({
      jsonrpc: '2.0',
      method: `${path}.update`,
      params: value,
    });
  });
  
  // Monitor balance for low balance notifications
  store.onStateChange((path, value) => {
    if (path === 'balance.venice.diem' && typeof value === 'number') {
      notificationService.notifyLowBalance(value);
    }
  });
  
  // Create Venice proxy and client (if API key available)
  let veniceProxy: VeniceProxy | null = null;
  let veniceClient: VeniceClient | null = null;
  if (config.venice.apiKey) {
    veniceProxy = new VeniceProxy(config.venice.apiKey, store);
    veniceClient = new VeniceClient(config.venice.apiKey, store);
    logger.info('Venice API proxy and client initialized');
  } else {
    logger.warn('Venice API key not provided, balance tracking disabled');
  }
  
  // Create OpenCode client
  const opencodeClient = await createOpenCodeClient(store, {
    baseUrl: config.opencode.apiUrl,
    directory: config.opencode.directory,
    fetch: globalThis.fetch,
  });
  if (opencodeClient) {
    logger.info('OpenCode client connected');
  } else {
    logger.warn('OpenCode client not available (SDK may not be installed)');
  }
  
  // Create Lean LSP proxy (if enabled)
  let leanProxy: LeanProxy | null = null;
  if (config.lean.enabled) {
    leanProxy = new LeanProxy(store);
    try {
      await leanProxy.connect(config.lean.command, config.lean.args);
      logger.info('Lean LSP proxy connected');
    } catch (error) {
      logger.warn('Lean LSP connection failed, continuing without Lean features:', error);
    }
  }
  
  // Create database manager
  const db = new DatabaseManager(config.storage.path);
  logger.info('Database initialized', { path: config.storage.path });
  
  // Wire persistence to state store
  const persistenceCleanup = wirePersistence(store, db);
  
  // Set handler context for WebSocket manager
  wsManager.setHandlerContext({
    store,
    veniceClient,
    leanProxy,
    db,
    notificationService,
  });
  
  // Start server
  server.listen(config.port, config.host, () => {
    logger.info('Bridge Server started', {
      port: config.port,
      host: config.host,
      wsPath: '/ws',
    });
  });
  
  // Graceful shutdown
  const shutdown = async () => {
    logger.info('Shutting down gracefully');
    
    // Stop voice service
    if (voiceService) {
      await voiceService.stop();
    }
    
    // Close WebSocket connections
    wsManager.close();
    
    // Disconnect Lean proxy
    if (leanProxy) {
      await leanProxy.disconnect();
    }
    
    // Cleanup persistence
    persistenceCleanup();
    
    // Close database
    db.close();
    
    // Close server
    server.close(() => {
      logger.info('Server closed');
      process.exit(0);
    });
  };
  
  process.on('SIGTERM', shutdown);
  process.on('SIGINT', shutdown);
}

main().catch((error) => {
  logger.error('Fatal error:', error);
  process.exit(1);
});
