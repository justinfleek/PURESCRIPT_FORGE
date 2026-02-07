"use strict";

// | Read a File object as text, returning a Promise
exports.readFileAsTextImpl = function(file) {
  return function() {
    return new Promise(function(resolve, reject) {
      if (!(file instanceof File)) {
        reject(new Error("Expected a File object"));
        return;
      }
      var reader = new FileReader();
      reader.onload = function(e) {
        resolve(e.target.result);
      };
      reader.onerror = function() {
        reject(new Error("Failed to read file: " + reader.error.message));
      };
      reader.readAsText(file);
    });
  };
};

// | Trigger native file picker and return selected file content as text
// | Returns a Promise that resolves with the file content string
// | or rejects if no file selected or reading fails
exports.triggerFilePickerImpl = function() {
  return new Promise(function(resolve, reject) {
    var input = document.createElement("input");
    input.type = "file";
    input.accept = ".json,.md,.sidepanel,.txt";
    input.style.display = "none";

    input.onchange = function(event) {
      var file = event.target.files[0];
      if (file) {
        var reader = new FileReader();
        reader.onload = function(e) {
          document.body.removeChild(input);
          resolve(e.target.result);
        };
        reader.onerror = function() {
          document.body.removeChild(input);
          reject(new Error("Failed to read file: " + reader.error.message));
        };
        reader.readAsText(file);
      } else {
        document.body.removeChild(input);
        reject(new Error("No file selected"));
      }
    };

    // Handle cancel (user closes dialog without selecting)
    input.oncancel = function() {
      document.body.removeChild(input);
      reject(new Error("File selection cancelled"));
    };

    document.body.appendChild(input);
    input.click();
  });
};

// | Fetch content from a URL as text
// | Returns a Promise that resolves with the response text
exports.fetchURLContentImpl = function(url) {
  return function() {
    return fetch(url)
      .then(function(response) {
        if (!response.ok) {
          throw new Error("HTTP " + response.status + ": " + response.statusText);
        }
        return response.text();
      });
  };
};
