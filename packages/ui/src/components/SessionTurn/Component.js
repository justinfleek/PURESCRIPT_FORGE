// Component.js - FFI for SessionTurn Component

// Copy text to clipboard
export const copyToClipboard = (text) => () => {
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text);
  }
};

// Force scroll to bottom
export const forceScrollToBottom = () => {
  // This would need access to the scroll container ref
  // In a real implementation, this would be passed from Halogen
};
