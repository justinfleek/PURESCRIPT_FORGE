// PRISM Color System FFI Implementation
// Calls Haskell prism-theme-generator binary via CLI
"use strict";

var child_process = require("child_process");
var path = require("path");

// Path to Haskell binary (built by Nix)
var PRISM_BINARY = process.env.PRISM_BINARY_PATH || "prism-theme-generator";

exports.generatePrismTheme = function(config) {
  try {
    // Convert PureScript config to JSON format expected by Haskell binary
    var jsonConfig = {
      baseColor: {
        hue: config.baseHue,
        saturation: config.baseSaturation,
        lightness: config.blackBalance || (config.monitorType === "OLED" ? 0.11 : 0.16)
      },
      heroColor: {
        hue: config.heroHue,
        saturation: config.heroSaturation,
        lightness: config.mode === "Dark" ? 0.66 : 0.50
      },
      monitorType: config.monitorType === "OLED" ? "OLED" : "LCD",
      blackBalance: config.blackBalance || (config.monitorType === "OLED" ? 0.11 : 0.16),
      mode: config.mode === "Dark" ? "dark" : "light"
    };
    
    // Call Haskell binary with JSON input
    var inputJson = JSON.stringify(jsonConfig);
    var result = child_process.spawnSync(PRISM_BINARY, ["generate"], {
      input: inputJson,
      encoding: "utf8",
      timeout: 5000
    });
    
    if (result.error) {
      console.error("PRISM generation error:", result.error);
      return getDefaultPalette();
    }
    
    if (result.status !== 0) {
      console.error("PRISM generation failed:", result.stderr);
      return getDefaultPalette();
    }
    
    // Parse output JSON
    var output = JSON.parse(result.stdout);
    
    // Extract first variant (or use default if none)
    if (output.variants && output.variants.length > 0) {
      var variant = output.variants[0];
      return variant.colors || getDefaultPalette();
    }
    
    return getDefaultPalette();
  } catch (e) {
    console.error("PRISM FFI error:", e);
    return getDefaultPalette();
  }
};

// Default palette fallback
function getDefaultPalette() {
  return {
    base00: "#1e1e1e",
    base01: "#252525",
    base02: "#2d2d2d",
    base03: "#3e3e3e",
    base04: "#858585",
    base05: "#cccccc",
    base06: "#e0e0e0",
    base07: "#ffffff",
    base08: "#ff6b6b",
    base09: "#ffa94d",
    base0A: "#54aeff",
    base0B: "#51cf66",
    base0C: "#4dabf7",
    base0D: "#339af0",
    base0E: "#ae3ec9",
    base0F: "#868e96"
  };
}
