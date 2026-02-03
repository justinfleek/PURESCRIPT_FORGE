// FFI implementations for Forge.UI.Theme.Loader
// Handles DOM manipulation for theme CSS injection

const THEME_STYLE_ID = "forge-theme";

// Active theme reference (module-level state)
let activeTheme = null;

// Ensure theme style element exists in document head
export const ensureLoaderStyleElement = () => {
  if (typeof document === "undefined") return;
  
  let style = document.getElementById(THEME_STYLE_ID);
  if (!style) {
    style = document.createElement("style");
    style.id = THEME_STYLE_ID;
    style.type = "text/css";
    document.head.appendChild(style);
  }
};

// Set style element content
export const setStyleContent = (css) => () => {
  if (typeof document === "undefined") return;
  
  const style = document.getElementById(THEME_STYLE_ID);
  if (style) {
    style.textContent = css;
  }
};

// Set document attribute
export const setDocumentAttribute = (name) => (value) => () => {
  if (typeof document === "undefined") return;
  document.documentElement.setAttribute(name, value);
};

// Remove document attribute
export const removeDocumentAttribute = (name) => () => {
  if (typeof document === "undefined") return;
  document.documentElement.removeAttribute(name);
};

// Get document attribute - returns Maybe String
export const getDocumentAttribute = (name) => () => {
  if (typeof document === "undefined") return null;
  const value = document.documentElement.getAttribute(name);
  return value; // PureScript FFI handles null -> Nothing conversion
};

// Set document style property
export const setDocumentStyleProperty = (name) => (value) => () => {
  if (typeof document === "undefined") return;
  document.documentElement.style.setProperty(name, value);
};

// Remove document style property
export const removeDocumentStyleProperty = (name) => () => {
  if (typeof document === "undefined") return;
  document.documentElement.style.removeProperty(name);
};

// Fetch JSON from URL - returns Aff
export const fetchJson = (url) => () => {
  return fetch(url)
    .then(response => {
      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }
      return response.json();
    });
};

// Get active theme reference
export const activeThemeRef = () => {
  return activeTheme;
};

// Set active theme reference
export const setActiveThemeRef = (theme) => () => {
  activeTheme = theme;
};

// Remove style element
export const removeStyleElement = () => {
  if (typeof document === "undefined") return;
  
  const style = document.getElementById(THEME_STYLE_ID);
  if (style) {
    style.remove();
  }
};
