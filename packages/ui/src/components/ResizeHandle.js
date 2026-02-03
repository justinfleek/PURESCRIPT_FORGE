// ResizeHandle FFI
// Minimal DOM operations for body style manipulation during resize

// Lock body styles to prevent text selection during drag
export const lockBodyStyles = () => {
  document.body.style.userSelect = "none";
  document.body.style.overflow = "hidden";
};

// Restore body styles after drag
export const restoreBodyStyles = () => {
  document.body.style.userSelect = "";
  document.body.style.overflow = "";
};
