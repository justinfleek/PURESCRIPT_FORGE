// FFI for Dialog Context
// Provides random ID generation

export const generateId = () => {
  return Math.random().toString(36).slice(2);
};

// Context reference placeholder - actual implementation uses Halogen
export const dialogContextRef = { current: null };
