// DiffChanges FFI
// Minimal array utilities

// Uncons: split array into head and tail
export const uncons = (arr) => {
  if (arr.length === 0) return null;
  return { head: arr[0], tail: arr.slice(1) };
};
