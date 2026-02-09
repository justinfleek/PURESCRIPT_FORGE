// | Agent Output Viewer FFI
// | JavaScript interop for clipboard, markdown rendering, etc.

"use strict";

// | Copy text to clipboard (async - returns Aff)
exports.copyToClipboard = function(text) {
  return function() {
    return new Promise(function(resolve, reject) {
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(text).then(function() {
          resolve({ tag: "Right", value: {} });
        }).catch(function(err) {
          resolve({ tag: "Left", value: err.message });
        });
      } else {
        // Fallback for older browsers
        var textArea = document.createElement("textarea");
        textArea.value = text;
        textArea.style.position = "fixed";
        textArea.style.left = "-999999px";
        textArea.style.top = "-999999px";
        document.body.appendChild(textArea);
        textArea.focus();
        textArea.select();
        try {
          document.execCommand('copy');
          document.body.removeChild(textArea);
          resolve({ tag: "Right", value: {} });
        } catch (err) {
          document.body.removeChild(textArea);
          resolve({ tag: "Left", value: err.message });
        }
      }
    });
  };
};

// | Render markdown to HTML (async - returns Aff)
// | Uses a simple markdown parser or falls back to HTML escaping
// | For production: Add markdown library (marked, markdown-it, marked-shiki, etc.)
exports.renderMarkdown = function(markdown) {
  return function() {
    return new Promise(function(resolve, reject) {
      try {
        // Simple markdown-to-HTML conversion
        // This is a basic implementation - for production, use a proper library
        var html = markdown
          // Escape HTML first
          .replace(/&/g, "&amp;")
          .replace(/</g, "&lt;")
          .replace(/>/g, "&gt;")
          // Then convert markdown patterns
          .replace(/^### (.*$)/gim, "<h3>$1</h3>")
          .replace(/^## (.*$)/gim, "<h2>$1</h2>")
          .replace(/^# (.*$)/gim, "<h1>$1</h1>")
          .replace(/\*\*(.*?)\*\*/g, "<strong>$1</strong>")
          .replace(/\*(.*?)\*/g, "<em>$1</em>")
          .replace(/`([^`]+)`/g, "<code>$1</code>")
          .replace(/```([\s\S]*?)```/g, "<pre><code>$1</code></pre>")
          .replace(/\n/g, "<br>");
        
        resolve(html);
      } catch (err) {
        // Fallback to escaped plain text on error
        resolve(markdown
          .replace(/&/g, "&amp;")
          .replace(/</g, "&lt;")
          .replace(/>/g, "&gt;")
        );
      }
    });
  };
};

// | Set innerHTML of element by ref label
// | Note: This requires the element to be rendered first
// | In production, use Halogen's H.getRef to get the element reference
exports.setInnerHTML = function(refLabel) {
  return function(html) {
    return function() {
      // Use requestAnimationFrame to ensure DOM is ready
      requestAnimationFrame(function() {
        // Halogen refs are stored in a special way - this is a simplified approach
        // For production: Use H.getRef in PureScript to get the actual element reference
        var element = document.querySelector("[ref='" + refLabel + "']");
        if (!element) {
          // Fallback: try to find by class or data attribute
          element = document.querySelector(".details-content");
        }
        if (element) {
          element.innerHTML = html;
        }
      });
    };
  };
};
