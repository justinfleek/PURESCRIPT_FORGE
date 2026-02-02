// | Set up keyboard shortcut handler
exports.setupKeyboardShortcuts = function(copyHandler, addToChatHandler) {
  return function() {
    const handler = function(event) {
      // Ctrl+C or Cmd+C - Copy
      if ((event.ctrlKey || event.metaKey) && event.key === "c" && !event.shiftKey) {
        const selection = window.getSelection();
        if (selection && !selection.isCollapsed) {
          event.preventDefault();
          copyHandler();
        }
      }
      
      // Ctrl+Enter or Cmd+Enter - Add to chat
      if ((event.ctrlKey || event.metaKey) && event.key === "Enter") {
        const selection = window.getSelection();
        if (selection && !selection.isCollapsed) {
          event.preventDefault();
          addToChatHandler();
        }
      }
    };
    
    document.addEventListener("keydown", handler);
    
    // Return cleanup function
    return function() {
      document.removeEventListener("keydown", handler);
    };
  };
};
