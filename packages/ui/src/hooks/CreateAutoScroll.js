// FFI for Auto Scroll Hook

// Get distance from bottom of scrollable element
export const distanceFromBottom = (el) => () => {
  return el.scrollHeight - el.clientHeight - el.scrollTop;
};

// Check if element can scroll
export const canScroll = (el) => () => {
  return el.scrollHeight - el.clientHeight > 1;
};

// Scroll element to bottom
export const scrollToBottomNow = (el) => (behavior) => () => {
  if (behavior === "smooth") {
    el.scrollTo({ top: el.scrollHeight, behavior });
  } else {
    // scrollTop assignment bypasses CSS scroll-behavior: smooth
    el.scrollTop = el.scrollHeight;
  }
};

// Add wheel event listener, returns cleanup function
export const addWheelListener = (el) => (callback) => () => {
  const handler = (e) => {
    callback(e.deltaY)();
  };
  el.addEventListener("wheel", handler, { passive: true });
  return () => {
    el.removeEventListener("wheel", handler);
  };
};

// Set overflow anchor style
export const setOverflowAnchor = (el) => (anchor) => () => {
  el.style.overflowAnchor = anchor;
};
