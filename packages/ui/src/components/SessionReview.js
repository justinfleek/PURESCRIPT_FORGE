// SessionReview.js - FFI for SessionReview component

// Get directory part of path
export const getDirectory = (path) => {
  if (!path) return "";
  const lastSlash = Math.max(path.lastIndexOf("/"), path.lastIndexOf("\\"));
  if (lastSlash === -1) return "";
  return path.slice(0, lastSlash + 1);
};

// Get filename part of path
export const getFilename = (path) => {
  if (!path) return "";
  const lastSlash = Math.max(path.lastIndexOf("/"), path.lastIndexOf("\\"));
  if (lastSlash === -1) return path;
  return path.slice(lastSlash + 1);
};

// Check if path contains slash
export const containsSlash = (path) => {
  if (!path) return false;
  return path.includes("/") || path.includes("\\");
};
