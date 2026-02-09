// Forge.Session.Compaction FFI - Session history compaction

// In-memory session message store (would be backed by real storage)
const sessionMessages = new Map();

// Get session messages
export const getSessionMessagesFFI = (sessionId) => async () => {
  return sessionMessages.get(sessionId) || [];
};

// Update session messages
export const updateSessionMessagesFFI = (sessionId) => (messages) => async () => {
  try {
    sessionMessages.set(sessionId, messages);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Summarize messages using LLM
export const summarizeMessagesFFI = (messages) => (model) => async () => {
  try {
    // In production, this would call the LLM API
    const summary = messages.map(m => 
      `[${m.role}]: ${m.content.slice(0, 100)}...`
    ).join('\n');
    
    return { tag: 'Right', value: `Summary of ${messages.length} messages:\n${summary}` };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Count tokens in a string (approximation)
export const countTokensFFI = (text) => {
  // Rough approximation: ~4 characters per token
  return Math.ceil(text.length / 4);
};
