// Timeline View FFI - Mouse event handling for scrubber
"use strict";

exports.calculateScrubPositionFromEvent = function(event) {
  return function() {
    try {
      // Get scrubber element
      const scrubber = event.currentTarget || event.target.closest('.timeline-scrubber');
      if (!scrubber) {
        return 0.0;
      }
      
      // Get scrubber bounds
      const rect = scrubber.getBoundingClientRect();
      const scrubberLeft = rect.left;
      const scrubberWidth = rect.width;
      
      // Get mouse X position
      const mouseX = event.clientX;
      
      // Calculate position (0-1)
      const position = (mouseX - scrubberLeft) / scrubberWidth;
      
      // Clamp to 0-1
      return Math.max(0.0, Math.min(1.0, position)) * 100.0; // Return as percentage 0-100
    } catch (e) {
      return 0.0;
    }
  };
};
