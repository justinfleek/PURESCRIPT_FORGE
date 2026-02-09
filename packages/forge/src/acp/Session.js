// Forge.ACP.Session FFI - Session management

import { randomUUID } from 'crypto';

// In-memory session store (in production, use persistent storage)
const sessionStore = new Map();
const messageStore = new Map();

// Create session
export const createSessionFFI = (sessionId) => (agentId) => (config) => async () => {
  try {
    const now = Date.now();
    const session = {
      id: sessionId,
      agentId,
      status: { tag: 'SessionActive' },
      config,
      createdAt: now,
      lastActivity: now
    };
    sessionStore.set(sessionId, session);
    messageStore.set(sessionId, []);
    return { tag: 'Right', value: mapSession(session) };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get session
export const getSessionFFI = (sessionId) => async () => {
  const session = sessionStore.get(sessionId);
  if (!session) return null;
  return mapSession(session);
};

// Update session status
export const updateSessionStatusFFI = (sessionId) => (statusStr) => async () => {
  try {
    const session = sessionStore.get(sessionId);
    if (!session) {
      return { tag: 'Left', value: `Session not found: ${sessionId}` };
    }
    session.status = parseStatus(statusStr);
    session.lastActivity = Date.now();
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Close session
export const closeSessionFFI = (sessionId) => async () => {
  try {
    const session = sessionStore.get(sessionId);
    if (!session) {
      return { tag: 'Left', value: `Session not found: ${sessionId}` };
    }
    session.status = { tag: 'SessionClosed' };
    // Optionally clean up after a delay
    setTimeout(() => {
      sessionStore.delete(sessionId);
      messageStore.delete(sessionId);
    }, 5000);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get active sessions
export const getActiveSessionsFFI = async () => {
  return Array.from(sessionStore.values())
    .filter(s => s.status.tag === 'SessionActive' || s.status.tag === 'SessionPaused')
    .map(mapSession);
};

// Add message to session
export const addMessageFFI = (sessionId) => (message) => async () => {
  try {
    const messages = messageStore.get(sessionId);
    if (!messages) {
      return { tag: 'Left', value: `Session not found: ${sessionId}` };
    }
    const msg = {
      ...message,
      timestamp: Date.now()
    };
    messages.push(msg);
    
    // Update session activity
    const session = sessionStore.get(sessionId);
    if (session) {
      session.lastActivity = Date.now();
    }
    
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get messages for session
export const getMessagesFFI = (sessionId) => async () => {
  const messages = messageStore.get(sessionId);
  return messages || [];
};

// Generate unique ID
export const generateIdFFI = async () => {
  return randomUUID();
};

// Traverse implementation
export const traverseImpl = (f) => (arr) => async () => {
  const results = [];
  for (const item of arr) {
    const result = await f(item)();
    results.push(result);
  }
  return results;
};

// Helper to map session to PureScript format
function mapSession(session) {
  return {
    id: session.id,
    agentId: session.agentId,
    status: mapStatus(session.status),
    config: session.config,
    createdAt: session.createdAt,
    lastActivity: session.lastActivity
  };
}

// Helper to map status
function mapStatus(status) {
  return status;
}

// Helper to parse status string
function parseStatus(str) {
  switch (str) {
    case 'creating': return { tag: 'SessionCreating' };
    case 'active': return { tag: 'SessionActive' };
    case 'paused': return { tag: 'SessionPaused' };
    case 'closing': return { tag: 'SessionClosing' };
    case 'closed': return { tag: 'SessionClosed' };
    default:
      if (str.startsWith('error:')) {
        return { tag: 'SessionError', value: str.slice(7) };
      }
      return { tag: 'SessionActive' };
  }
}
