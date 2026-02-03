// FFI for Theme Context

// Get system color mode preference
export const getSystemMode = () => {
  return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
};

// Apply theme CSS to document
export const applyThemeCss = (css) => (themeId) => (mode) => () => {
  const fullCss = `:root {
  color-scheme: ${mode};
  --text-mix-blend-mode: ${mode === "dark" ? "plus-lighter" : "multiply"};
  ${css}
}`;

  // Remove preload style if exists
  document.getElementById("forge-theme-preload")?.remove();
  
  // Ensure theme style element exists
  let styleEl = document.getElementById("forge-theme");
  if (!styleEl) {
    styleEl = document.createElement("style");
    styleEl.id = "forge-theme";
    document.head.appendChild(styleEl);
  }
  styleEl.textContent = fullCss;
  
  // Set data attributes
  document.documentElement.dataset.theme = themeId;
  document.documentElement.dataset.colorScheme = mode;
};

// Store value in localStorage
export const setStorageItem = (key) => (value) => () => {
  try {
    localStorage.setItem(key, value);
  } catch (e) {
    // Ignore storage errors
  }
};

// Get value from localStorage
export const getStorageItem = (key) => () => {
  try {
    const value = localStorage.getItem(key);
    return value ? { value0: value } : null;
  } catch (e) {
    return null;
  }
};

// Context reference placeholder
export const themeContextRef = { current: null };
