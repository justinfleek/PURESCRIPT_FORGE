// Component.js - FFI for MessagePart Component

// Check if string starts with prefix
export const startsWith = (prefix) => (str) => {
  if (!str || !prefix) return false;
  return str.startsWith(prefix);
};

// Copy text to clipboard
export const copyToClipboard = (text) => () => {
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text);
  }
};
