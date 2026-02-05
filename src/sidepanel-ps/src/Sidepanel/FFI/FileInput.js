"use strict";

exports.readFileAsText = function(filePath) {
  return function() {
    return new Promise(function(resolve, reject) {
      // This would need to be called with a File object from input element
      // For now, placeholder
      reject("File reading not yet implemented");
    });
  };
};

exports.triggerFilePicker = function() {
  return function() {
    // Create file input element and trigger click
    var input = document.createElement("input");
    input.type = "file";
    input.accept = ".json,.md,.sidepanel";
    input.onchange = function(event) {
      var file = event.target.files[0];
      if (file) {
        var reader = new FileReader();
        reader.onload = function(e) {
          // Would need to pass result back via callback
        };
        reader.readAsText(file);
      }
    };
    input.click();
  };
};
