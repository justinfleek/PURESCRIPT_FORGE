// | Copy text to clipboard
exports.copyToClipboard = function(text) {
  return function() {
    // Try modern clipboard API first
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).catch(function() {
        // Fallback to execCommand if clipboard API fails
        fallbackCopy(text);
      });
      return;
    }
    
    // Fallback for older browsers
    fallbackCopy(text);
  };
};

function fallbackCopy(text) {
  const textarea = document.createElement("textarea");
  textarea.value = text;
  textarea.style.position = "fixed";
  textarea.style.opacity = "0";
  textarea.style.pointerEvents = "none";
  document.body.appendChild(textarea);
  textarea.select();
  
  try {
    document.execCommand("copy");
  } catch (err) {
    // Ignore errors
  }
  
  document.body.removeChild(textarea);
}

// | Get selected text from window
exports.getSelection = function() {
  return function() {
    const selection = window.getSelection();
    if (!selection || selection.isCollapsed) {
      return null;
    }
    return selection.toString();
  };
};
