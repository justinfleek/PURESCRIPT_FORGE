// List FFI
// Minimal utilities for array operations

// Map array with index
export const mapWithIndexImpl = (arr) => {
  return arr.map((value, index) => ({ index, value }));
};
