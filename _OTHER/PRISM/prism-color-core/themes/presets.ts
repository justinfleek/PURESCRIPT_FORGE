/**
 * Prism Theme Generator - Preset Themes
 * 
 * Curated collection of harmonious and experimental themes
 * inspired by Niutonian Themes and Enhanced Links & Nodes
 */

import type { ThemeConfig, ThemeVariant } from "./types";

// =============================================================================
// Types
// =============================================================================

export interface ThemeEffects {
  glow?: boolean;
  glowIntensity?: number;
  glowColor?: string;
  glass?: boolean;
  glassOpacity?: number;
  glassBlur?: number;
  glassSaturation?: number;
  scanlines?: boolean;
  chromatic_aberration?: number;
  gradient?: string[];
  animation?: "pulse" | "flow" | "ripple" | "sacred" | "spark" | "shimmer";
}

export interface WCAGInfo {
  level: "A" | "AA" | "AAA";
  textContrast: number;
  uiContrast: number;
}

export interface ColorblindInfo {
  type: "protanopia" | "deuteranopia" | "tritanopia";
  avoidHues: number[];
  useHues: number[];
}

export interface ThemePreset {
  name: string;
  category: "harmonious" | "wild" | "glassmorphism" | "monochromatic" | "accessibility";
  inspiration: string;
  baseColor: { hue: number; saturation: number; lightness: number };
  heroColor: { hue: number; saturation: number; lightness: number };
  monitorType: "OLED" | "LCD";
  blackBalance: number;
  mode: "dark" | "light";
  tags: string[];
  effects?: ThemeEffects;
  wcag?: WCAGInfo;
  colorblindSafe?: ColorblindInfo;
}

// =============================================================================
// Harmonious Themes - Classic color theory
// =============================================================================

export const HARMONIOUS_THEMES: Record<string, ThemePreset> = {
  ocean_depths: {
    name: "Ocean Depths",
    category: "harmonious",
    inspiration: "Deep sea bioluminescence meets midnight water",
    baseColor: { hue: 220, saturation: 0.15, lightness: 0.08 },
    heroColor: { hue: 185, saturation: 0.95, lightness: 0.65 },
    monitorType: "OLED",
    blackBalance: 0.08,
    mode: "dark",
    tags: ["calm", "professional", "deep"],
    effects: { glow: true, glowIntensity: 0.2, glowColor: "#61e8e1" }
  },

  forest_canopy: {
    name: "Forest Canopy",
    category: "harmonious",
    inspiration: "Dappled sunlight through ancient trees",
    baseColor: { hue: 140, saturation: 0.12, lightness: 0.09 },
    heroColor: { hue: 85, saturation: 0.85, lightness: 0.58 },
    monitorType: "OLED",
    blackBalance: 0.09,
    mode: "dark",
    tags: ["natural", "calm", "organic"]
  },

  sunset_ember: {
    name: "Sunset Ember",
    category: "harmonious",
    inspiration: "Warm coals and golden hour",
    baseColor: { hue: 25, saturation: 0.18, lightness: 0.10 },
    heroColor: { hue: 35, saturation: 0.92, lightness: 0.62 },
    monitorType: "OLED",
    blackBalance: 0.10,
    mode: "dark",
    tags: ["warm", "cozy", "focused"],
    effects: { glow: true, glowIntensity: 0.15, glowColor: "#ffb347" }
  },

  lavender_dusk: {
    name: "Lavender Dusk",
    category: "harmonious",
    inspiration: "Twilight purple meeting soft blue",
    baseColor: { hue: 270, saturation: 0.14, lightness: 0.11 },
    heroColor: { hue: 280, saturation: 0.78, lightness: 0.68 },
    monitorType: "OLED",
    blackBalance: 0.11,
    mode: "dark",
    tags: ["elegant", "creative", "soft"],
    effects: { glow: true, glowIntensity: 0.18, glowColor: "#b388ff" }
  },

  arctic_aurora: {
    name: "Arctic Aurora",
    category: "harmonious",
    inspiration: "Northern lights over ice fields",
    baseColor: { hue: 200, saturation: 0.10, lightness: 0.06 },
    heroColor: { hue: 160, saturation: 0.88, lightness: 0.55 },
    monitorType: "OLED",
    blackBalance: 0.06,
    mode: "dark",
    tags: ["cold", "ethereal", "magical"],
    effects: { glow: true, glowIntensity: 0.25, glowColor: "#69f0ae" }
  },

  rose_quartz: {
    name: "Rose Quartz",
    category: "harmonious",
    inspiration: "Soft pink crystals in morning light",
    baseColor: { hue: 350, saturation: 0.08, lightness: 0.12 },
    heroColor: { hue: 340, saturation: 0.72, lightness: 0.70 },
    monitorType: "LCD",
    blackBalance: 0.12,
    mode: "dark",
    tags: ["gentle", "warm", "feminine"]
  },

  slate_and_gold: {
    name: "Slate & Gold",
    category: "harmonious",
    inspiration: "Luxury minimalism - precious metal on stone",
    baseColor: { hue: 220, saturation: 0.05, lightness: 0.14 },
    heroColor: { hue: 45, saturation: 0.95, lightness: 0.58 },
    monitorType: "LCD",
    blackBalance: 0.14,
    mode: "dark",
    tags: ["professional", "luxury", "minimal"],
    effects: { glow: true, glowIntensity: 0.12, glowColor: "#ffd700" }
  },

  gentle_pulse: {
    name: "Gentle Pulse",
    category: "harmonious",
    inspiration: "Calm blue energy flow",
    baseColor: { hue: 220, saturation: 0.12, lightness: 0.11 },
    heroColor: { hue: 210, saturation: 0.90, lightness: 0.60 },
    monitorType: "OLED",
    blackBalance: 0.11,
    mode: "dark",
    tags: ["calm", "focused", "reliable"],
    effects: { glow: true, glowIntensity: 0.15, glowColor: "#44aaff", animation: "pulse" }
  }
};

// =============================================================================
// Wild Themes - Breaking conventional rules
// =============================================================================

export const WILD_THEMES: Record<string, ThemePreset> = {
  cyberpunk_2099: {
    name: "Cyberpunk 2099",
    category: "wild",
    inspiration: "Neon-soaked dystopian megacity",
    baseColor: { hue: 280, saturation: 0.08, lightness: 0.04 },
    heroColor: { hue: 320, saturation: 1.0, lightness: 0.55 },
    monitorType: "OLED",
    blackBalance: 0.04,
    mode: "dark",
    tags: ["aggressive", "futuristic", "neon"],
    effects: {
      glow: true,
      glowIntensity: 0.35,
      glowColor: "#ff00ff",
      scanlines: true,
      chromatic_aberration: 0.02
    }
  },

  neon_nexus: {
    name: "Neon Nexus",
    category: "wild",
    inspiration: "Matrix-style digital green rain",
    baseColor: { hue: 140, saturation: 0.15, lightness: 0.03 },
    heroColor: { hue: 145, saturation: 1.0, lightness: 0.52 },
    monitorType: "OLED",
    blackBalance: 0.03,
    mode: "dark",
    tags: ["hacker", "matrix", "digital"],
    effects: { glow: true, glowIntensity: 0.40, glowColor: "#00ff88", animation: "flow" }
  },

  cosmic_ripple: {
    name: "Cosmic Ripple",
    category: "wild",
    inspiration: "Galactic nebulae and dark matter",
    baseColor: { hue: 280, saturation: 0.20, lightness: 0.05 },
    heroColor: { hue: 300, saturation: 1.0, lightness: 0.58 },
    monitorType: "OLED",
    blackBalance: 0.05,
    mode: "dark",
    tags: ["cosmic", "psychedelic", "deep"],
    effects: { glow: true, glowIntensity: 0.30, glowColor: "#aa00ff", animation: "ripple" }
  },

  flower_of_life: {
    name: "Flower of Life",
    category: "wild",
    inspiration: "Sacred geometry in amber and gold",
    baseColor: { hue: 35, saturation: 0.25, lightness: 0.06 },
    heroColor: { hue: 42, saturation: 1.0, lightness: 0.55 },
    monitorType: "OLED",
    blackBalance: 0.06,
    mode: "dark",
    tags: ["sacred", "warm", "ancient"],
    effects: { glow: true, glowIntensity: 0.25, glowColor: "#ffcc00", animation: "sacred" }
  },

  vaporwave_sunset: {
    name: "Vaporwave Sunset",
    category: "wild",
    inspiration: "Retro 80s aesthetics meets future nostalgia",
    baseColor: { hue: 260, saturation: 0.22, lightness: 0.08 },
    heroColor: { hue: 180, saturation: 1.0, lightness: 0.50 },
    monitorType: "OLED",
    blackBalance: 0.08,
    mode: "dark",
    tags: ["retro", "nostalgic", "aesthetic"],
    effects: {
      glow: true,
      glowIntensity: 0.28,
      glowColor: "#00ffff",
      gradient: ["#ff6b9d", "#c44dff", "#00ffff"],
      scanlines: true
    }
  },

  blood_moon: {
    name: "Blood Moon",
    category: "wild",
    inspiration: "Lunar eclipse crimson darkness",
    baseColor: { hue: 0, saturation: 0.25, lightness: 0.05 },
    heroColor: { hue: 5, saturation: 0.95, lightness: 0.48 },
    monitorType: "OLED",
    blackBalance: 0.05,
    mode: "dark",
    tags: ["dark", "intense", "dramatic"],
    effects: { glow: true, glowIntensity: 0.22, glowColor: "#ff1744" }
  },

  electric_dreams: {
    name: "Electric Dreams",
    category: "wild",
    inspiration: "Synth-wave electricity arcing through circuits",
    baseColor: { hue: 240, saturation: 0.18, lightness: 0.06 },
    heroColor: { hue: 55, saturation: 1.0, lightness: 0.58 },
    monitorType: "OLED",
    blackBalance: 0.06,
    mode: "dark",
    tags: ["electric", "contrast", "energetic"],
    effects: { glow: true, glowIntensity: 0.32, glowColor: "#ffea00", animation: "spark" }
  },

  acid_rain: {
    name: "Acid Rain",
    category: "wild",
    inspiration: "Toxic green dripping through industrial night",
    baseColor: { hue: 80, saturation: 0.15, lightness: 0.04 },
    heroColor: { hue: 75, saturation: 1.0, lightness: 0.48 },
    monitorType: "OLED",
    blackBalance: 0.04,
    mode: "dark",
    tags: ["toxic", "industrial", "edgy"],
    effects: { glow: true, glowIntensity: 0.38, glowColor: "#c6ff00" }
  },

  holographic: {
    name: "Holographic",
    category: "wild",
    inspiration: "Iridescent light diffraction patterns",
    baseColor: { hue: 260, saturation: 0.12, lightness: 0.10 },
    heroColor: { hue: 180, saturation: 0.85, lightness: 0.62 },
    monitorType: "OLED",
    blackBalance: 0.10,
    mode: "dark",
    tags: ["iridescent", "futuristic", "dynamic"],
    effects: {
      glow: true,
      glowIntensity: 0.20,
      glowColor: "#00ffff",
      gradient: ["#ff0080", "#8000ff", "#0080ff", "#00ff80"],
      animation: "shimmer"
    }
  },

  ultraviolet: {
    name: "Ultraviolet",
    category: "wild",
    inspiration: "Blacklight poster in a dark room",
    baseColor: { hue: 270, saturation: 0.30, lightness: 0.03 },
    heroColor: { hue: 275, saturation: 1.0, lightness: 0.60 },
    monitorType: "OLED",
    blackBalance: 0.03,
    mode: "dark",
    tags: ["blacklight", "psychedelic", "trippy"],
    effects: { glow: true, glowIntensity: 0.45, glowColor: "#bf00ff" }
  }
};

// =============================================================================
// Glassmorphism Themes
// =============================================================================

export const GLASS_THEMES: Record<string, ThemePreset> = {
  frosted_midnight: {
    name: "Frosted Midnight",
    category: "glassmorphism",
    inspiration: "Frosted glass over night cityscape",
    baseColor: { hue: 230, saturation: 0.15, lightness: 0.12 },
    heroColor: { hue: 200, saturation: 0.90, lightness: 0.58 },
    monitorType: "OLED",
    blackBalance: 0.12,
    mode: "dark",
    tags: ["modern", "elegant", "translucent"],
    effects: {
      glass: true,
      glassOpacity: 0.85,
      glassSaturation: 1.2,
      glassBlur: 12,
      glow: true,
      glowIntensity: 0.18,
      glowColor: "#00d4ff"
    }
  },

  crystal_cave: {
    name: "Crystal Cave",
    category: "glassmorphism",
    inspiration: "Translucent crystals in underground cavern",
    baseColor: { hue: 270, saturation: 0.18, lightness: 0.14 },
    heroColor: { hue: 280, saturation: 0.82, lightness: 0.65 },
    monitorType: "OLED",
    blackBalance: 0.14,
    mode: "dark",
    tags: ["crystalline", "mystical", "elegant"],
    effects: {
      glass: true,
      glassOpacity: 0.88,
      glassBlur: 16,
      glow: true,
      glowIntensity: 0.22,
      glowColor: "#e040fb"
    }
  },

  smoke_and_mirrors: {
    name: "Smoke & Mirrors",
    category: "glassmorphism",
    inspiration: "Smoky glass with subtle reflections",
    baseColor: { hue: 0, saturation: 0.0, lightness: 0.15 },
    heroColor: { hue: 0, saturation: 0.0, lightness: 0.75 },
    monitorType: "LCD",
    blackBalance: 0.15,
    mode: "dark",
    tags: ["neutral", "sophisticated", "minimal"],
    effects: { glass: true, glassOpacity: 0.90, glassBlur: 10 }
  }
};

// =============================================================================
// Light Themes
// =============================================================================

export const LIGHT_THEMES: Record<string, ThemePreset> = {
  paper_and_ink: {
    name: "Paper & Ink",
    category: "harmonious",
    inspiration: "Classic manuscript on cream paper",
    baseColor: { hue: 45, saturation: 0.15, lightness: 0.95 },
    heroColor: { hue: 220, saturation: 0.85, lightness: 0.35 },
    monitorType: "LCD",
    blackBalance: 0.05,
    mode: "light",
    tags: ["classic", "readable", "literary"]
  },

  morning_frost: {
    name: "Morning Frost",
    category: "harmonious",
    inspiration: "Ice crystals catching first sunlight",
    baseColor: { hue: 200, saturation: 0.08, lightness: 0.96 },
    heroColor: { hue: 200, saturation: 0.75, lightness: 0.45 },
    monitorType: "LCD",
    blackBalance: 0.04,
    mode: "light",
    tags: ["clean", "crisp", "professional"]
  },

  solar_flare: {
    name: "Solar Flare",
    category: "wild",
    inspiration: "Sun-bleached with vibrant orange accents",
    baseColor: { hue: 45, saturation: 0.10, lightness: 0.97 },
    heroColor: { hue: 25, saturation: 0.95, lightness: 0.52 },
    monitorType: "LCD",
    blackBalance: 0.03,
    mode: "light",
    tags: ["bright", "energetic", "warm"]
  }
};

// =============================================================================
// Accessibility Themes
// =============================================================================

export const ACCESSIBILITY_THEMES: Record<string, ThemePreset> = {
  high_contrast_dark: {
    name: "High Contrast Dark",
    category: "accessibility",
    inspiration: "Maximum readability, WCAG AAA compliant",
    baseColor: { hue: 0, saturation: 0.0, lightness: 0.0 },
    heroColor: { hue: 55, saturation: 1.0, lightness: 0.55 },
    monitorType: "OLED",
    blackBalance: 0.0,
    mode: "dark",
    tags: ["accessible", "high-contrast", "wcag-aaa"],
    wcag: { level: "AAA", textContrast: 15.2, uiContrast: 12.8 }
  },

  high_contrast_light: {
    name: "High Contrast Light",
    category: "accessibility",
    inspiration: "Bright with maximum text contrast",
    baseColor: { hue: 0, saturation: 0.0, lightness: 1.0 },
    heroColor: { hue: 220, saturation: 1.0, lightness: 0.35 },
    monitorType: "LCD",
    blackBalance: 0.0,
    mode: "light",
    tags: ["accessible", "high-contrast", "wcag-aaa"],
    wcag: { level: "AAA", textContrast: 16.5, uiContrast: 14.2 }
  },

  deuteranopia_safe: {
    name: "Deuteranopia Safe",
    category: "accessibility",
    inspiration: "Optimized for red-green color blindness",
    baseColor: { hue: 220, saturation: 0.10, lightness: 0.11 },
    heroColor: { hue: 45, saturation: 0.90, lightness: 0.55 },
    monitorType: "OLED",
    blackBalance: 0.11,
    mode: "dark",
    tags: ["accessible", "colorblind-safe", "deuteranopia"],
    colorblindSafe: { type: "deuteranopia", avoidHues: [0, 120], useHues: [45, 220, 280] }
  }
};

// =============================================================================
// All Themes Combined
// =============================================================================

export const ALL_THEMES: Record<string, ThemePreset> = {
  ...HARMONIOUS_THEMES,
  ...WILD_THEMES,
  ...GLASS_THEMES,
  ...LIGHT_THEMES,
  ...ACCESSIBILITY_THEMES
};

// =============================================================================
// Helper Functions
// =============================================================================

/**
 * Convert a preset to ThemeConfig format used by the generator
 */
export function presetToConfig(preset: ThemePreset): ThemeConfig {
  return {
    baseColor: {
      hue: preset.baseColor.hue,
      saturation: preset.baseColor.saturation,
      lightness: preset.baseColor.lightness
    },
    heroColor: {
      hue: preset.heroColor.hue,
      saturation: preset.heroColor.saturation,
      lightness: preset.heroColor.lightness
    },
    monitorType: preset.monitorType,
    blackBalance: preset.blackBalance,
    mode: preset.mode
  };
}

/**
 * Get themes filtered by category
 */
export function getThemesByCategory(category: ThemePreset["category"]): ThemePreset[] {
  return Object.values(ALL_THEMES).filter(t => t.category === category);
}

/**
 * Get themes filtered by tag
 */
export function getThemesByTag(tag: string): ThemePreset[] {
  return Object.values(ALL_THEMES).filter(t => t.tags.includes(tag));
}

/**
 * Get theme by ID
 */
export function getThemeById(id: string): ThemePreset | undefined {
  return ALL_THEMES[id];
}

/**
 * Search themes by name or inspiration
 */
export function searchThemes(query: string): ThemePreset[] {
  const q = query.toLowerCase();
  return Object.values(ALL_THEMES).filter(t =>
    t.name.toLowerCase().includes(q) ||
    t.inspiration.toLowerCase().includes(q) ||
    t.tags.some(tag => tag.includes(q))
  );
}

// =============================================================================
// Exports
// =============================================================================

export default {
  harmonious: HARMONIOUS_THEMES,
  wild: WILD_THEMES,
  glass: GLASS_THEMES,
  light: LIGHT_THEMES,
  accessibility: ACCESSIBILITY_THEMES,
  all: ALL_THEMES,
  presetToConfig,
  getThemesByCategory,
  getThemesByTag,
  getThemeById,
  searchThemes
};
