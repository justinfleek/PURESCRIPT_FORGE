// Forge.Session.Retry FFI - Retry logic

// Get a specific message
export const getMessageFFI = (sessionId) => (messageId) => async () => {
  // Placeholder - in production would fetch from session store
  return null;
};

// Resend a message
export const resendMessageFFI = (sessionId) => (messageId) => async () => {
  // Placeholder - in production would trigger message resend
  return { tag: 'Right', value: {} };
};

// Get messages from a specific point
export const getMessagesFromFFI = (sessionId) => (fromMessageId) => async () => {
  // Placeholder - in production would fetch from session store
  return [];
};

// Generate random number between 0 and 1
export const randomFFI = async () => {
  return Math.random();
};

// Check if string contains substring (case insensitive)
export const containsImpl = (needle) => (haystack) => {
  return haystack.toLowerCase().includes(needle.toLowerCase());
};

// Power function
export const powImpl = (base) => (exp) => {
  return Math.pow(base, exp);
};

// Int to Number
export const toNumberImpl = (n) => n;

// Floor
export const floorImpl = (n) => Math.floor(n);
