// DropdownMenu FFI - Array utilities

/**
 * Take first n elements from array
 * @param {number} n
 * @returns {(arr: Array) => Array}
 */
export const takeImpl = (n) => (arr) => arr.slice(0, n);

/**
 * Delete element at index
 * @param {number} idx
 * @returns {(arr: Array) => Array | null}
 */
export const deleteAtImpl = (idx) => (arr) => {
  if (idx < 0 || idx >= arr.length) return null;
  const result = [...arr];
  result.splice(idx, 1);
  return result;
};

/**
 * Get element at index
 * @param {Array} arr
 * @returns {(idx: number) => any | null}
 */
export const indexArrayImpl = (arr) => (idx) => {
  if (idx < 0 || idx >= arr.length) return null;
  return arr[idx];
};
