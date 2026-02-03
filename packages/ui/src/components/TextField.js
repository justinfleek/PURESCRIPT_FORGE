// TextField FFI - Clipboard API
// Legitimate DOM operation: browser clipboard access

/**
 * Copy text to clipboard using the Clipboard API
 * @param {string} text - Text to copy
 * @returns {() => void}
 */
export const copyToClipboard = (text) => () => {
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text).catch((err) => {
      // Fallback for older browsers or when clipboard API fails
      fallbackCopy(text);
    });
  } else {
    fallbackCopy(text);
  }
};

/**
 * Fallback copy using textarea + execCommand
 * For browsers without Clipboard API support
 * @param {string} text
 */
function fallbackCopy(text) {
  const textarea = document.createElement('textarea');
  textarea.value = text;
  textarea.style.position = 'fixed';
  textarea.style.left = '-9999px';
  textarea.style.top = '-9999px';
  document.body.appendChild(textarea);
  textarea.focus();
  textarea.select();
  try {
    document.execCommand('copy');
  } catch (err) {
    // Silent fail - copy not supported
  }
  document.body.removeChild(textarea);
}
