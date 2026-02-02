/**
 * OpenCode Client - Complete Implementation
 * Connects to OpenCode via SDK v2 and forwards events to state store
 */
import { StateStore } from '../state/store.js';
import { handleOpenCodeEvent } from './events.js';
import pino from 'pino';

const logger = pino({ name: 'opencode-client' });

// OpenCode SDK v2 types (based on actual SDK structure)
interface OpenCodeSDK {
  event: {
    subscribe(params: {}, options: { signal?: AbortSignal }): Promise<{
      stream: AsyncIterable<Event>;
    }>;
  };
  connect(): Promise<void>;
  disconnect(): Promise<void>;
}

interface Event {
  type: string;
  payload?: Record<string, unknown>;
  session?: SessionData;
  message?: MessageData;
  tool?: ToolData;
  path?: string;
  // Note: Using Record<string, unknown> instead of any for type safety
  [key: string]: unknown;
}

interface SessionData {
  id: string;
  promptTokens?: number;
  completionTokens?: number;
  totalTokens?: number;
  cost?: number;
  model?: string;
  provider?: string;
  messageCount?: number;
  createdAt?: string | Date;
  updatedAt?: string | Date;
  tokenUsage?: {
    promptTokens: number;
    completionTokens: number;
    totalTokens: number;
  };
}

interface MessageData {
  id: string;
  sessionId?: string;
  usage?: {
    promptTokens: number;
    completionTokens: number;
    totalTokens: number;
  };
  cost?: number;
  status?: string;
}

interface ToolData {
  name: string;
  duration?: number;
  result?: unknown;
}

/**
 * Create and configure OpenCode client
 */
export async function createOpenCodeClient(
  store: StateStore,
  config?: {
    baseUrl?: string;
    directory?: string;
    fetch?: typeof globalThis.fetch;
  }
): Promise<OpenCodeSDK | null> {
  try {
    // Import actual OpenCode SDK v2
    // Note: This will work when @opencode-ai/sdk is available
    const { createOpencodeClient } = await import('@opencode-ai/sdk/v2');
    
    const baseUrl = config?.baseUrl ?? 'http://opencode.internal';
    const directory = config?.directory ?? process.cwd();
    const fetchFn = config?.fetch ?? globalThis.fetch;
    
    logger.info('Creating OpenCode client', { baseUrl, directory });
    
    const sdk = createOpencodeClient({
      baseUrl,
      directory,
      fetch: fetchFn,
    });
    
    // Subscribe to events
    const abortController = new AbortController();
    
    // Start event subscription loop
    (async () => {
      while (!abortController.signal.aborted) {
        try {
          logger.debug('Subscribing to OpenCode events');
          
          const events = await sdk.event.subscribe({}, {
            signal: abortController.signal,
          });
          
          logger.info('OpenCode event stream connected');
          
          for await (const event of events.stream) {
            if (abortController.signal.aborted) {
              break;
            }
            
            try {
              handleOpenCodeEvent(store, event);
              logger.debug('Processed OpenCode event', { type: event.type });
            } catch (error) {
              logger.error('Error handling OpenCode event', {
                error: error instanceof Error ? error.message : String(error),
                type: event.type,
              });
            }
          }
          
          logger.warn('OpenCode event stream ended, reconnecting...');
        } catch (error) {
          if (abortController.signal.aborted) {
            break;
          }
          
          logger.error('OpenCode event stream error', {
            error: error instanceof Error ? error.message : String(error),
          });
          
          // Wait before retrying
          await new Promise(resolve => setTimeout(resolve, 1000));
        }
      }
      
      logger.info('OpenCode event subscription loop ended');
    })();
    
    // Connect SDK
    await sdk.connect();
    logger.info('OpenCode SDK connected');
    
    // Cleanup on shutdown
    const shutdown = () => {
      logger.info('Shutting down OpenCode client');
      abortController.abort();
      sdk.disconnect().catch((error) => {
        logger.error('Error disconnecting OpenCode SDK', {
          error: error instanceof Error ? error.message : String(error),
        });
      });
    };
    
    process.on('SIGTERM', shutdown);
    process.on('SIGINT', shutdown);
    
    return sdk;
  } catch (error) {
    // If SDK import fails, log warning but don't crash
    logger.warn('OpenCode SDK not available, continuing without OpenCode events', {
      error: error instanceof Error ? error.message : String(error),
    });
    
    // Return null to indicate SDK unavailable
    return null;
  }
}
