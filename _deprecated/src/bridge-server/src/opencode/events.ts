/**
 * OpenCode Event Handlers
 * Maps OpenCode SDK events to state store updates
 */
import { StateStore, SessionState } from '../state/store.js';

// Event types (based on OpenCode SDK structure)
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

interface Event {
  type: string;
  payload?: Record<string, unknown>;
  session?: SessionData;
  message?: MessageData;
  tool?: ToolData;
  path?: string;
  [key: string]: unknown;
}

/**
 * Map OpenCode event to state store update
 */
export function handleOpenCodeEvent(store: StateStore, event: Event): void {
  switch (event.type) {
    case 'session.created':
      handleSessionCreated(store, event);
      break;
    
    case 'session.updated':
      handleSessionUpdated(store, event);
      break;
    
    case 'session.deleted':
      handleSessionDeleted(store, event);
      break;
    
    case 'message.created':
    case 'message.updated':
    case 'message.completed':
      handleMessageEvent(store, event);
      break;
    
    case 'tool.execute.before':
    case 'tool.execute.after':
      handleToolEvent(store, event);
      break;
    
    case 'file.read':
    case 'file.write':
    case 'file.delete':
      handleFileEvent(store, event);
      break;
    
    case 'provider.request.start':
    case 'provider.request.end':
    case 'provider.error':
      handleProviderEvent(store, event);
      break;
    
    default:
      // Unknown event type, log but don't crash
      // This is acceptable - OpenCode may add new event types
      if (process.env.NODE_ENV === 'development') {
        console.debug('Unknown OpenCode event type:', event.type);
      }
  }
}

/**
 * Handle session.created event
 */
function handleSessionCreated(store: StateStore, event: Event): void {
  const session = event.session ?? (event.payload as { session?: SessionData })?.session;
  if (!session || typeof session !== 'object' || !('id' in session) || typeof session.id !== 'string') {
    console.warn('session.created event missing session data');
    return;
  }
  
  store.updateSession({
    id: session.id,
    promptTokens: session.promptTokens ?? session.tokenUsage?.promptTokens ?? 0,
    completionTokens: session.completionTokens ?? session.tokenUsage?.completionTokens ?? 0,
    totalTokens: session.totalTokens ?? session.tokenUsage?.totalTokens ?? 0,
    cost: session.cost ?? 0,
    model: session.model ?? '',
    provider: session.provider ?? '',
    messageCount: session.messageCount ?? 0,
    startedAt: session.createdAt ? new Date(session.createdAt) : new Date(),
    updatedAt: session.updatedAt ? new Date(session.updatedAt) : new Date(),
  });
}

/**
 * Handle session.updated event
 */
function handleSessionUpdated(store: StateStore, event: any): void {
  const session = event.session ?? event.payload?.session;
  if (!session || !session.id) {
    console.warn('session.updated event missing session data');
    return;
  }
  
  const current = store.getState().session;
  if (!current || current.id !== session.id) {
    // Session doesn't match current, ignore or create new
    handleSessionCreated(store, event);
    return;
  }
  
  store.updateSession({
    promptTokens: session.promptTokens ?? session.tokenUsage?.promptTokens ?? current.promptTokens,
    completionTokens: session.completionTokens ?? session.tokenUsage?.completionTokens ?? current.completionTokens,
    totalTokens: session.totalTokens ?? session.tokenUsage?.totalTokens ?? current.totalTokens,
    cost: session.cost ?? current.cost,
    messageCount: session.messageCount ?? current.messageCount,
    updatedAt: session.updatedAt ? new Date(session.updatedAt) : new Date(),
  });
}

/**
 * Handle session.deleted event
 */
function handleSessionDeleted(store: StateStore, event: any): void {
  store.clearSession();
}

/**
 * Handle message events
 */
function handleMessageEvent(store: StateStore, event: any): void {
  const message = event.message ?? event.payload?.message;
  if (!message) {
    return;
  }
  
  const current = store.getState().session;
  if (!current) {
    return;
  }
  
  // Update session with message usage
  if (message.usage && event.type === 'message.completed') {
    store.updateSession({
      promptTokens: current.promptTokens + (message.usage.promptTokens ?? 0),
      completionTokens: current.completionTokens + (message.usage.completionTokens ?? 0),
      totalTokens: current.totalTokens + (message.usage.totalTokens ?? 0),
      messageCount: current.messageCount + 1,
    });
    
    // Update metrics
    const metrics = store.getState().metrics;
    store.updateMetrics({
      totalTokens: metrics.totalTokens + (message.usage.totalTokens ?? 0),
      totalCost: metrics.totalCost + (message.cost ?? 0),
    });
  }
}

/**
 * Handle tool execution events
 */
function handleToolEvent(store: StateStore, event: any): void {
  const tool = event.tool ?? event.payload?.tool;
  const duration = event.duration ?? event.payload?.duration;
  
  if (!tool || !duration) {
    return;
  }
  
  // Update tool timings
  const metrics = store.getState().metrics;
  const timings = { ...metrics.toolTimings };
  
  // Calculate running average
  const existing = timings[tool] ?? 0;
  const count = Object.keys(timings).length;
  timings[tool] = count > 0 ? (existing + duration) / 2 : duration;
  
  store.updateMetrics({ toolTimings: timings });
}

/**
 * Handle file events
 */
function handleFileEvent(store: StateStore, event: any): void {
  const path = event.path ?? event.payload?.path;
  if (!path) {
    return;
  }
  
  // Check if Lean4 file
  if (path.endsWith('.lean') && event.type === 'file.write') {
    // Trigger Lean check (will be handled by Lean proxy)
    // For now, just log
    console.debug('Lean4 file written:', path);
  }
}

/**
 * Handle provider events
 */
function handleProviderEvent(store: StateStore, event: Event): void {
  const provider = (event.payload as { provider?: string })?.provider;
  const response = (event.payload as { response?: Record<string, unknown> })?.response;
  const error = (event.payload as { error?: Error })?.error;
  
  if (!provider) {
    return;
  }
  
  switch (event.type) {
    case 'provider.request.start':
      // Track provider usage
      const metrics = store.getState().metrics;
      store.updateMetrics({
        ...metrics,
        // Could track provider-specific metrics here
      });
      break;
    
    case 'provider.request.end':
      // Extract balance from Venice responses
      if (provider === 'venice' && response) {
        // Balance extraction is handled by Venice proxy directly
        // This handler is for other providers or additional processing
        const headers = (response as { headers?: Record<string, string> })?.headers;
        if (headers) {
          // Could extract balance from headers here if needed
          // But Venice proxy already handles this
        }
      }
      break;
    
    case 'provider.error':
      // Log provider errors
      if (error) {
        console.error(`Provider ${provider} error:`, error);
      }
      // Update connection state if critical error
      if (provider === 'venice') {
        // Venice errors are handled by Venice proxy
        // This is for logging/tracking
      }
      break;
  }
}
