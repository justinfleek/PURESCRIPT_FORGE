// | Inject CSS into document head
export const injectCSS = function(css) {
  return function() {
    const styleId = "forge-sidepanel-theme";
    let styleElement = document.getElementById(styleId);

    if (!styleElement) {
      styleElement = document.createElement("style");
      styleElement.id = styleId;
      styleElement.setAttribute("type", "text/css");
      document.head.appendChild(styleElement);
    }

    styleElement.textContent = css;
  };
};

// | Get or create style element for theme
export const ensureThemeStyleElement = function() {
  return function() {
    const styleId = "forge-sidepanel-theme";
    let styleElement = document.getElementById(styleId);

    if (!styleElement) {
      styleElement = document.createElement("style");
      styleElement.id = styleId;
      styleElement.setAttribute("type", "text/css");
      document.head.appendChild(styleElement);
    }
  };
};
