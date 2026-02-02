/**
 * WebSocket Message Handlers
 * 
 * Production-grade handlers for all WebSocket JSON-RPC methods.
 * These handlers integrate with StateStore, VeniceClient, LeanProxy, etc.
 */
import { StateStore } from '../state/store.js';
import { VeniceClient } from '../venice/client.js';
import { LeanProxy } from '../lean/proxy.js';
import { DatabaseManager } from '../database/schema.js';
import { NotificationService } from '../notifications/service.js';
import { handleOpenCodeEvent } from '../opencode/events.js';
import pino from 'pino';

const logger = pino({ name: 'ws-handlers' });

export interface HandlerContext {
  store: StateStore;
  veniceClient: VeniceClient | null;
  leanProxy: LeanProxy | null;
  db: DatabaseManager;
  notificationService: NotificationService;
}

/**
 * Handle OpenCode event from plugin
 */
export async function handleOpenCodeEventMessage(
  context: HandlerContext,
  params: { event: unknown }
): Promise<{ success: boolean }> {
  try {
    // Forward event to state store handler
    handleOpenCodeEvent(context.store, params.event as { type: string; [key: string]: unknown });
    
    logger.debug('OpenCode event processed', { eventType: (params.event as { type?: string })?.type });
    
    return { success: true };
  } catch (error) {
    logger.error('Failed to handle OpenCode event', { error });
    throw error;
  }
}

/**
 * Handle Venice chat completion request
 */
export async function handleVeniceChat(
  context: HandlerContext,
  params: {
    model: string;
    messages: Array<{ role: string; content: string }>;
    stream?: boolean;
    max_tokens?: number;
    temperature?: number;
  }
): Promise<unknown> {
  if (!context.veniceClient) {
    throw new Error('Venice API client not available');
  }
  
  const request = {
    model: params.model,
    messages: params.messages as Array<{ role: 'system' | 'user' | 'assistant'; content: string }>,
    max_tokens: params.max_tokens,
    temperature: params.temperature,
    stream: params.stream ?? false,
  };
  
  if (request.stream) {
    // For streaming, we need to handle this differently
    // Return a stream ID and handle chunks via notifications
    const streamId = `stream-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
    
    // Start streaming in background
    (async () => {
      try {
        for await (const chunk of context.veniceClient.chatStream(request)) {
          context.notificationService.notify({
            type: 'silent',
            level: 'info',
            title: 'Venice Stream Chunk',
            message: JSON.stringify(chunk),
            group: streamId,
          });
        }
      } catch (error) {
        logger.error('Streaming error', { error, streamId });
        context.notificationService.error('Streaming error', error instanceof Error ? error.message : String(error));
      }
    })();
    
    return { streamId, type: 'stream' };
  } else {
    // Non-streaming: return complete response
    const response = await context.veniceClient.chat(request);
    return response;
  }
}

/**
 * Handle Venice model listing request
 */
export async function handleVeniceModels(
  context: HandlerContext,
  params: Record<string, unknown>
): Promise<unknown> {
  if (!context.veniceClient) {
    throw new Error('Venice API client not available');
  }
  
  const models = await context.veniceClient.listModels();
  return { models };
}

/**
 * Handle Venice image generation request
 */
export async function handleVeniceImage(
  context: HandlerContext,
  params: {
    model: string;
    prompt: string;
    width?: number;
    height?: number;
    seed?: number;
  }
): Promise<unknown> {
  if (!context.veniceClient) {
    throw new Error('Venice API client not available');
  }
  
  const response = await context.veniceClient.generateImage({
    model: params.model,
    prompt: params.prompt,
    width: params.width,
    height: params.height,
    seed: params.seed,
  });
  
  return response;
}

/**
 * Handle notification dismiss request
 */
export async function handleNotificationDismiss(
  context: HandlerContext,
  params: { id: string }
): Promise<{ success: boolean }> {
  context.notificationService.dismiss(params.id);
  return { success: true };
}

/**
 * Handle notification dismiss all request
 */
export async function handleNotificationDismissAll(
  context: HandlerContext,
  params: Record<string, unknown>
): Promise<{ success: boolean }> {
  context.notificationService.dismissAll();
  return { success: true };
}

/**
 * Handle balance refresh request
 */
export async function handleBalanceRefresh(
  context: HandlerContext,
  params: Record<string, unknown>
): Promise<unknown> {
  const state = context.store.getState();
  return {
    balance: state.balance,
    timestamp: new Date().toISOString(),
  };
}

/**
 * Handle session list request
 */
export async function handleSessionList(
  context: HandlerContext,
  params: Record<string, unknown>
): Promise<unknown> {
  const state = context.store.getState();
  const limit = typeof params.limit === 'number' ? params.limit : 100;
  
  // Get sessions from database
  const sessions = context.db.getAllSessions(limit);
  
  return {
    sessions: sessions.map(s => ({
      id: s.sessionId,
      model: s.model,
      provider: s.provider,
      promptTokens: s.promptTokens,
      completionTokens: s.completionTokens,
      totalTokens: s.promptTokens + s.completionTokens,
      cost: s.cost,
      startedAt: s.startedAt.toISOString(),
      endedAt: s.endedAt ? s.endedAt.toISOString() : null,
    })),
    currentSession: state.session,
  };
}

/**
 * Handle proof status request
 */
export async function handleProofStatus(
  context: HandlerContext,
  params: { file?: string }
): Promise<unknown> {
  const state = context.store.getState();
  return {
    goals: state.proof.goals,
    diagnostics: state.proof.diagnostics,
    file: params.file,
  };
}
