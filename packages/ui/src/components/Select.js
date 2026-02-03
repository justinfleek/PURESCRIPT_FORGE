// Select FFI - Array utilities

/**
 * Get array length
 * @param {Array} arr
 * @returns {number}
 */
export const arrayLengthImpl = (arr) => arr.length;

/**
 * Find index of string in array
 * @param {string} needle
 * @returns {(arr: string[]) => number | null}
 */
export const findIndexImpl = (needle) => (arr) => {
  const idx = arr.indexOf(needle);
  return idx === -1 ? null : idx;
};

/**
 * Get element at index
 * @param {Array} arr
 * @returns {(idx: number) => any | null}
 */
export const arrayIndexImpl = (arr) => (idx) => {
  if (idx < 0 || idx >= arr.length) return null;
  return arr[idx];
};
