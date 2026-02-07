// | Download FFI Implementation
// | Provides file download functionality
"use strict";

// | Download file with content and filename
exports.downloadFile = function(content) {
  return function(filename) {
    return function() {
      const blob = new Blob([content], { type: "text/plain;charset=utf-8" });
      const url = URL.createObjectURL(blob);
      const link = document.createElement("a");
      link.href = url;
      link.download = filename;
      document.body.appendChild(link);
      link.click();
      document.body.removeChild(link);
      URL.revokeObjectURL(url);
    };
  };
};
