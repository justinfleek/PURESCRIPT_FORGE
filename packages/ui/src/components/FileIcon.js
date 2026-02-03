// FileIcon FFI - String and Array utilities

/**
 * Get last element of array (unsafe - assumes non-empty)
 * @param {Array} arr
 * @returns {any}
 */
export const unsafeLastImpl = (arr) => arr[arr.length - 1];

/**
 * Check if string starts with prefix
 * @param {string} prefix
 * @returns {(str: string) => boolean}
 */
export const startsWithImpl = (prefix) => (str) => str.startsWith(prefix);

/**
 * Get head of array
 * @param {Array} arr
 * @returns {any | null}
 */
export const arrayHeadImpl = (arr) => arr.length > 0 ? arr[0] : null;

/**
 * Get tail of array
 * @param {Array} arr
 * @returns {Array}
 */
export const arrayTailImpl = (arr) => arr.slice(1);

/**
 * Get all dotted suffixes from a filename, longest first
 * @param {string} name
 * @returns {string[]}
 */
export const getDottedSuffixesImpl = (name) => {
  const n = name.toLowerCase();
  const indices = [];
  for (let i = 0; i < n.length; i++) {
    if (n[i] === '.') indices.push(i);
  }
  const out = new Set();
  out.add(n); // Allow exact whole-name matches like "dockerfile"
  for (const i of indices) {
    if (i + 1 < n.length) out.add(n.slice(i + 1));
  }
  return Array.from(out).sort((a, b) => b.length - a.length); // Longest first
};
