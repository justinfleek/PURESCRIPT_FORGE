// | Inject CSS into document head
exports.injectCSS = function(css) {
  return function() {
    const styleId = "opencode-sidepanel-theme";
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
exports.ensureThemeStyleElement = function() {
  return function() {
    const styleId = "opencode-sidepanel-theme";
    let styleElement = document.getElementById(styleId);
    
    if (!styleElement) {
      styleElement = document.createElement("style");
      styleElement.id = styleId;
      styleElement.setAttribute("type", "text/css");
      document.head.appendChild(styleElement);
    }
  };
};

// | Inject CSS with specific ID
exports.injectCSSWithId = function(id) {
  return function(css) {
    return function() {
      let styleElement = document.getElementById(id);
      
      if (!styleElement) {
        styleElement = document.createElement("style");
        styleElement.id = id;
        styleElement.setAttribute("type", "text/css");
        document.head.appendChild(styleElement);
      }
      
      styleElement.textContent = css;
    };
  };
};

// | Set CSS custom property (variable) on document root
exports.setCSSVariable = function(varName) {
  return function(value) {
    return function() {
      document.documentElement.style.setProperty(varName, value);
    };
  };
};
