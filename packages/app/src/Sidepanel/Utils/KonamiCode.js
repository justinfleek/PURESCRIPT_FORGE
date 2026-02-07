"use strict";

// Create Konami code detector
exports.createDetector = function(callback) {
  return function() {
    var sequence = [];
    var listener = null;
    
    var onKeyDown = function(event) {
      var key = event.key;
      var keyCode = null;
      
      if (key === "ArrowUp") keyCode = "ArrowUp";
      else if (key === "ArrowDown") keyCode = "ArrowDown";
      else if (key === "ArrowLeft") keyCode = "ArrowLeft";
      else if (key === "ArrowRight") keyCode = "ArrowRight";
      else if (key === "b" || key === "B") keyCode = "KeyB";
      else if (key === "a" || key === "A") keyCode = "KeyA";
      else return;
      
      sequence.push(keyCode);
      
      // Konami code: Up Up Down Down Left Right Left Right B A
      var konamiCode = ["ArrowUp", "ArrowUp", "ArrowDown", "ArrowDown", 
                        "ArrowLeft", "ArrowRight", "ArrowLeft", "ArrowRight", 
                        "KeyB", "KeyA"];
      
      // Check if sequence matches
      if (sequence.length >= konamiCode.length) {
        var match = true;
        for (var i = 0; i < konamiCode.length; i++) {
          if (sequence[sequence.length - konamiCode.length + i] !== konamiCode[i]) {
            match = false;
            break;
          }
        }
        
        if (match) {
          callback();
          sequence = []; // Reset
          return;
        }
      }
      
      // Check if still matching prefix
      var prefixLength = Math.min(sequence.length, konamiCode.length);
      var stillMatching = true;
      for (var i = 0; i < prefixLength; i++) {
        if (sequence[i] !== konamiCode[i]) {
          stillMatching = false;
          break;
        }
      }
      
      // Reset if not matching
      if (!stillMatching) {
        sequence = [];
      }
      
      // Keep last 10 keys max
      if (sequence.length > 10) {
        sequence = sequence.slice(-10);
      }
    };
    
    document.addEventListener("keydown", onKeyDown);
    
    return {
      sequence: sequence,
      callback: callback,
      listener: onKeyDown
    };
  };
};

// Destroy detector
exports.destroyDetector = function(detector) {
  return function() {
    if (detector && detector.listener) {
      document.removeEventListener("keydown", detector.listener);
    }
  };
};
