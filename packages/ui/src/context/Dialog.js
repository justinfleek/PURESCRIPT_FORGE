// FFI for Dialog Context
// Provides random ID generation

export const generateId = () => {
  return Math.random().toString(36).slice(2);
};

// Context reference for dialog state (Halogen-managed lifecycle)
export const dialogContextRef = { current: null };
