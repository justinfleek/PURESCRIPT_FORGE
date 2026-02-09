// Timeline View FFI - Mouse event handling for scrubber

// Convert a PureScript DateTime to a JS timestamp (milliseconds since epoch)
export const toTimestampImpl = function(dt) {
  // PureScript DateTime comes as a JS Date object from the FFI boundary
  if (dt instanceof Date) {
    return dt.getTime();
  }
  // If it's already a number, return it
  if (typeof dt === 'number') {
    return dt;
  }
  // Fallback: try to parse as string
  return new Date(String(dt)).getTime() || 0;
};

export const calculateScrubPositionFromEvent = function(event) {
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
