import * as vscode from "vscode";
import { ThemeConfig, ThemeVariant } from "./types";

/**
 * Luxury preset definitions imported from prism-color-core
 * These are the premium themes with effects metadata
 */
export interface PresetEffects {
  glow?: boolean;
  glowIntensity?: number;
  glowColor?: string;
  glass?: boolean;
  glassBlur?: number;
  glassOpacity?: number;
  particles?: {
    enabled: boolean;
    type: string;
    count: number;
    color: string;
    speed: number;
  };
  neumorphism?: {
    enabled: boolean;
    lightColor: string;
    shadowColor: string;
    distance: number;
    blur: number;
  };
}

export interface Base16Palette {
  base00: string;
  base01: string;
  base02: string;
  base03: string;
  base04: string;
  base05: string;
  base06: string;
  base07: string;
  base08: string;
  base09: string;
  base0A: string;
  base0B: string;
  base0C: string;
  base0D: string;
  base0E: string;
  base0F: string;
}

export interface ThemePreset {
  id: string;
  name: string;
  category: "luxury" | "glass" | "bento" | "neumorphism" | "responsive" | "easter_eggs";
  inspiration: string;
  baseColor: { hue: number; saturation: number; lightness: number };
  heroColor: { hue: number; saturation: number; lightness: number };
  monitorType: "OLED" | "LCD";
  blackBalance: number;
  mode: "dark" | "light";
  tags: string[];
  palette: Base16Palette;
  effects?: PresetEffects;
}

// =============================================================================
// LUXURY MARBLE PRESETS
// =============================================================================

export const LUXURY_PRESETS: ThemePreset[] = [
  {
    id: "nero_marquina",
    name: "Nero Marquina",
    category: "luxury",
    inspiration: "Black Spanish marble with white veining and warm gold leaf accents",
    baseColor: { hue: 220, saturation: 0.06, lightness: 0.04 },
    heroColor: { hue: 45, saturation: 0.85, lightness: 0.55 },
    monitorType: "OLED",
    blackBalance: 0.04,
    mode: "dark",
    tags: ["luxury", "marble", "gold", "premium"],
    palette: {
      base00: "#08080a",
      base01: "#101014",
      base02: "#18181e",
      base03: "#3a3a45",
      base04: "#5a5a68",
      base05: "#e8e4dc",
      base06: "#f5f2ea",
      base07: "#fffef8",
      base08: "#e85454",
      base09: "#e8a054",
      base0A: "#d4af37",
      base0B: "#54c878",
      base0C: "#54b4b8",
      base0D: "#5494e8",
      base0E: "#b454e8",
      base0F: "#a89050"
    },
    effects: {
      glow: true,
      glowIntensity: 0.08,
      glowColor: "#d4af37",
      particles: {
        enabled: true,
        type: "gold-dust",
        count: 4,
        color: "#d4af3725",
        speed: 0.15
      }
    }
  },
  {
    id: "obsidian_rose_gold",
    name: "Obsidian Rose Gold",
    category: "luxury",
    inspiration: "Volcanic glass with delicate rose gold veining",
    baseColor: { hue: 340, saturation: 0.08, lightness: 0.03 },
    heroColor: { hue: 15, saturation: 0.55, lightness: 0.68 },
    monitorType: "OLED",
    blackBalance: 0.03,
    mode: "dark",
    tags: ["luxury", "obsidian", "rose-gold", "feminine"],
    palette: {
      base00: "#050404",
      base01: "#0c0a0a",
      base02: "#141210",
      base03: "#3a3535",
      base04: "#5a5555",
      base05: "#f0e8e8",
      base06: "#f8f2f2",
      base07: "#fffafa",
      base08: "#e87878",
      base09: "#e8a878",
      base0A: "#e8b4b8",
      base0B: "#78c8a8",
      base0C: "#78b8c8",
      base0D: "#7898e8",
      base0E: "#c878e8",
      base0F: "#a88878"
    },
    effects: {
      glow: true,
      glowIntensity: 0.06,
      glowColor: "#e8b4b8"
    }
  },
  {
    id: "midnight_sapphire",
    name: "Midnight Sapphire",
    category: "luxury",
    inspiration: "Deep blue gemstone with platinum accents and inner fire",
    baseColor: { hue: 230, saturation: 0.40, lightness: 0.04 },
    heroColor: { hue: 220, saturation: 0.85, lightness: 0.62 },
    monitorType: "OLED",
    blackBalance: 0.04,
    mode: "dark",
    tags: ["luxury", "sapphire", "platinum", "royal"],
    palette: {
      base00: "#050810",
      base01: "#0a1018",
      base02: "#101825",
      base03: "#2a3548",
      base04: "#4a5568",
      base05: "#e0e8f8",
      base06: "#f0f4ff",
      base07: "#fafcff",
      base08: "#f87171",
      base09: "#fb923c",
      base0A: "#c0c0d0",
      base0B: "#6ee7b7",
      base0C: "#67e8f9",
      base0D: "#60a5fa",
      base0E: "#a78bfa",
      base0F: "#8090a0"
    },
    effects: {
      glow: true,
      glowIntensity: 0.12,
      glowColor: "#60a5fa"
    }
  },
  {
    id: "emerald_velvet",
    name: "Emerald Velvet",
    category: "luxury",
    inspiration: "Rich emerald on black velvet with gold filigree",
    baseColor: { hue: 160, saturation: 0.18, lightness: 0.04 },
    heroColor: { hue: 145, saturation: 0.75, lightness: 0.48 },
    monitorType: "OLED",
    blackBalance: 0.04,
    mode: "dark",
    tags: ["luxury", "emerald", "velvet", "opulent"],
    palette: {
      base00: "#040806",
      base01: "#081008",
      base02: "#101810",
      base03: "#283828",
      base04: "#485848",
      base05: "#e0f0e0",
      base06: "#f0fff0",
      base07: "#f8fff8",
      base08: "#f87171",
      base09: "#d4af37",
      base0A: "#d4af37",
      base0B: "#50c878",
      base0C: "#5fd4b8",
      base0D: "#60a5fa",
      base0E: "#a78bfa",
      base0F: "#8fa878"
    },
    effects: {
      glow: true,
      glowIntensity: 0.10,
      glowColor: "#50c878"
    }
  },
  {
    id: "champagne_noir",
    name: "Champagne Noir",
    category: "luxury",
    inspiration: "Matte black with rising champagne gold bubbles",
    baseColor: { hue: 45, saturation: 0.04, lightness: 0.05 },
    heroColor: { hue: 48, saturation: 0.75, lightness: 0.65 },
    monitorType: "OLED",
    blackBalance: 0.05,
    mode: "dark",
    tags: ["luxury", "champagne", "celebration"],
    palette: {
      base00: "#0a0a08",
      base01: "#121210",
      base02: "#1a1a18",
      base03: "#3a3a35",
      base04: "#5a5a55",
      base05: "#f0ece0",
      base06: "#f8f4e8",
      base07: "#fffff0",
      base08: "#e86060",
      base09: "#e89060",
      base0A: "#f7e7ce",
      base0B: "#60c080",
      base0C: "#60b0c0",
      base0D: "#6090e0",
      base0E: "#a060e0",
      base0F: "#a09060"
    },
    effects: {
      glow: true,
      glowIntensity: 0.08,
      glowColor: "#f7e7ce",
      particles: {
        enabled: true,
        type: "champagne-bubbles",
        count: 3,
        color: "#f7e7ce20",
        speed: 0.08
      }
    }
  }
];

// =============================================================================
// GLASSMORPHISM PRESETS
// =============================================================================

export const GLASS_PRESETS: ThemePreset[] = [
  {
    id: "aurora_glass",
    name: "Aurora Glass",
    category: "glass",
    inspiration: "Northern lights through frosted ice panels",
    baseColor: { hue: 260, saturation: 0.25, lightness: 0.06 },
    heroColor: { hue: 160, saturation: 0.85, lightness: 0.55 },
    monitorType: "OLED",
    blackBalance: 0.06,
    mode: "dark",
    tags: ["glass", "aurora", "magical"],
    palette: {
      base00: "#0a0815",
      base01: "#12101f",
      base02: "#1a1828",
      base03: "#3a3550",
      base04: "#5a5570",
      base05: "#e8f0f8",
      base06: "#f0f8ff",
      base07: "#faffff",
      base08: "#f87171",
      base09: "#fb923c",
      base0A: "#a78bfa",
      base0B: "#4ade80",
      base0C: "#22d3ee",
      base0D: "#60a5fa",
      base0E: "#c084fc",
      base0F: "#64ffda"
    },
    effects: {
      glass: true,
      glassBlur: 20,
      glassOpacity: 0.72,
      glow: true,
      glowIntensity: 0.06,
      glowColor: "#64ffda"
    }
  },
  {
    id: "diamond_dust",
    name: "Diamond Dust",
    category: "glass",
    inspiration: "Ice crystals catching light like scattered diamonds",
    baseColor: { hue: 210, saturation: 0.18, lightness: 0.05 },
    heroColor: { hue: 200, saturation: 0.90, lightness: 0.62 },
    monitorType: "OLED",
    blackBalance: 0.05,
    mode: "dark",
    tags: ["glass", "diamond", "sparkle"],
    palette: {
      base00: "#08090d",
      base01: "#0f1118",
      base02: "#161922",
      base03: "#303540",
      base04: "#505560",
      base05: "#e8f0ff",
      base06: "#f0f8ff",
      base07: "#fafeff",
      base08: "#f87171",
      base09: "#fb923c",
      base0A: "#38bdf8",
      base0B: "#4ade80",
      base0C: "#22d3ee",
      base0D: "#60a5fa",
      base0E: "#818cf8",
      base0F: "#94a3b8"
    },
    effects: {
      glass: true,
      glassBlur: 24,
      glassOpacity: 0.68,
      particles: {
        enabled: true,
        type: "diamond-sparkle",
        count: 5,
        color: "#ffffff40",
        speed: 0.02
      }
    }
  }
];

// =============================================================================
// BENTO PRESETS
// =============================================================================

export const BENTO_PRESETS: ThemePreset[] = [
  {
    id: "tokyo_night_bento",
    name: "Tokyo Night Bento",
    category: "bento",
    inspiration: "Japanese minimalism meets neon-lit cityscape",
    baseColor: { hue: 230, saturation: 0.28, lightness: 0.07 },
    heroColor: { hue: 280, saturation: 0.85, lightness: 0.68 },
    monitorType: "OLED",
    blackBalance: 0.07,
    mode: "dark",
    tags: ["bento", "japanese", "neon"],
    palette: {
      base00: "#0f0f18",
      base01: "#16161f",
      base02: "#1e1e28",
      base03: "#3a3a4a",
      base04: "#5a5a6a",
      base05: "#e8e8f0",
      base06: "#f0f0f8",
      base07: "#fafaff",
      base08: "#f7768e",
      base09: "#ff9e64",
      base0A: "#e0af68",
      base0B: "#9ece6a",
      base0C: "#73daca",
      base0D: "#7aa2f7",
      base0E: "#bb9af7",
      base0F: "#c792ea"
    },
    effects: {
      glow: true,
      glowIntensity: 0.10,
      glowColor: "#bb9af7"
    }
  },
  {
    id: "zen_garden",
    name: "Zen Garden",
    category: "bento",
    inspiration: "Raked sand, moss, and stone in perfect balance",
    baseColor: { hue: 80, saturation: 0.08, lightness: 0.09 },
    heroColor: { hue: 90, saturation: 0.45, lightness: 0.52 },
    monitorType: "OLED",
    blackBalance: 0.09,
    mode: "dark",
    tags: ["bento", "zen", "peaceful"],
    palette: {
      base00: "#101210",
      base01: "#181a18",
      base02: "#202220",
      base03: "#404540",
      base04: "#606560",
      base05: "#e8f0e8",
      base06: "#f0f8f0",
      base07: "#f8fff8",
      base08: "#e87878",
      base09: "#d4a870",
      base0A: "#c8b878",
      base0B: "#78b878",
      base0C: "#70b8a8",
      base0D: "#7090b8",
      base0E: "#a078a0",
      base0F: "#8a9878"
    }
  }
];

// =============================================================================
// NEUMORPHISM PRESETS
// =============================================================================

export const NEUMORPHISM_PRESETS: ThemePreset[] = [
  {
    id: "soft_charcoal",
    name: "Soft Charcoal",
    category: "neumorphism",
    inspiration: "Pressed surfaces in warm charcoal clay",
    baseColor: { hue: 220, saturation: 0.08, lightness: 0.18 },
    heroColor: { hue: 35, saturation: 0.80, lightness: 0.55 },
    monitorType: "LCD",
    blackBalance: 0.18,
    mode: "dark",
    tags: ["neumorphism", "soft", "tactile"],
    palette: {
      base00: "#2a2a32",
      base01: "#2a2a32",
      base02: "#32323a",
      base03: "#50505a",
      base04: "#70707a",
      base05: "#e8e8f0",
      base06: "#f0f0f8",
      base07: "#fafaff",
      base08: "#f87171",
      base09: "#fb923c",
      base0A: "#fbbf24",
      base0B: "#4ade80",
      base0C: "#22d3ee",
      base0D: "#60a5fa",
      base0E: "#a78bfa",
      base0F: "#9ca3af"
    },
    effects: {
      neumorphism: {
        enabled: true,
        lightColor: "rgba(58,58,66,0.5)",
        shadowColor: "rgba(18,18,22,0.7)",
        distance: 6,
        blur: 12
      }
    }
  },
  {
    id: "porcelain_moon",
    name: "Porcelain Moon",
    category: "neumorphism",
    inspiration: "Fine bone china in soft moonlight",
    baseColor: { hue: 220, saturation: 0.05, lightness: 0.92 },
    heroColor: { hue: 220, saturation: 0.65, lightness: 0.45 },
    monitorType: "LCD",
    blackBalance: 0.08,
    mode: "light",
    tags: ["neumorphism", "light", "delicate"],
    palette: {
      base00: "#e8eaee",
      base01: "#e8eaee",
      base02: "#dfe1e5",
      base03: "#a0a4aa",
      base04: "#707478",
      base05: "#1a1c20",
      base06: "#101214",
      base07: "#050608",
      base08: "#dc2626",
      base09: "#ea580c",
      base0A: "#ca8a04",
      base0B: "#16a34a",
      base0C: "#0891b2",
      base0D: "#2563eb",
      base0E: "#7c3aed",
      base0F: "#6b7280"
    },
    effects: {
      neumorphism: {
        enabled: true,
        lightColor: "rgba(255,255,255,0.8)",
        shadowColor: "rgba(163,177,198,0.5)",
        distance: 8,
        blur: 16
      }
    }
  }
];

// =============================================================================
// RESPONSIVE PRESETS
// =============================================================================

export const RESPONSIVE_PRESETS: ThemePreset[] = [
  {
    id: "ember_hearth",
    name: "Ember Hearth",
    category: "responsive",
    inspiration: "Warm fireplace with embers responding to activity",
    baseColor: { hue: 15, saturation: 0.22, lightness: 0.06 },
    heroColor: { hue: 25, saturation: 0.95, lightness: 0.58 },
    monitorType: "OLED",
    blackBalance: 0.06,
    mode: "dark",
    tags: ["responsive", "warm", "cozy"],
    palette: {
      base00: "#0c0908",
      base01: "#141010",
      base02: "#1c1614",
      base03: "#3a302a",
      base04: "#5a4a40",
      base05: "#f8f0e0",
      base06: "#fff8e8",
      base07: "#fffff0",
      base08: "#ff6b6b",
      base09: "#ffa94d",
      base0A: "#ffd93d",
      base0B: "#6bcb77",
      base0C: "#4d96ff",
      base0D: "#ff8c42",
      base0E: "#c792ea",
      base0F: "#ffb347"
    },
    effects: {
      glow: true,
      glowIntensity: 0.14,
      glowColor: "#ff6b35",
      particles: {
        enabled: true,
        type: "embers",
        count: 4,
        color: "#ff6b3530",
        speed: 0.1
      }
    }
  },
  {
    id: "tide_pool",
    name: "Tide Pool",
    category: "responsive",
    inspiration: "Bioluminescent creatures responding to movement",
    baseColor: { hue: 200, saturation: 0.28, lightness: 0.05 },
    heroColor: { hue: 175, saturation: 0.92, lightness: 0.52 },
    monitorType: "OLED",
    blackBalance: 0.05,
    mode: "dark",
    tags: ["responsive", "ocean", "bioluminescent"],
    palette: {
      base00: "#06090c",
      base01: "#0c1218",
      base02: "#121a20",
      base03: "#283540",
      base04: "#485560",
      base05: "#e0f0f8",
      base06: "#f0faff",
      base07: "#f8ffff",
      base08: "#f87171",
      base09: "#fb923c",
      base0A: "#40e0d0",
      base0B: "#00ff88",
      base0C: "#00d4ff",
      base0D: "#40e0d0",
      base0E: "#a78bfa",
      base0F: "#64ffda"
    },
    effects: {
      glow: true,
      glowIntensity: 0.14,
      glowColor: "#40e0d0",
      particles: {
        enabled: true,
        type: "bioluminescent",
        count: 5,
        color: "#40e0d030",
        speed: 0.05
      }
    }
  }
];

// =============================================================================
// EASTER EGG PRESETS
// =============================================================================

export const EASTER_EGG_PRESETS: ThemePreset[] = [
  {
    id: "constellation_map",
    name: "Constellation Map",
    category: "easter_eggs",
    inspiration: "Star charts with connections forming over time",
    baseColor: { hue: 230, saturation: 0.18, lightness: 0.04 },
    heroColor: { hue: 45, saturation: 0.88, lightness: 0.62 },
    monitorType: "OLED",
    blackBalance: 0.04,
    mode: "dark",
    tags: ["easter-egg", "stars", "discovery"],
    palette: {
      base00: "#050608",
      base01: "#0a0c10",
      base02: "#10141a",
      base03: "#283040",
      base04: "#485060",
      base05: "#e8f0ff",
      base06: "#f0f8ff",
      base07: "#fafeff",
      base08: "#f87171",
      base09: "#fbbf24",
      base0A: "#ffd700",
      base0B: "#4ade80",
      base0C: "#22d3ee",
      base0D: "#60a5fa",
      base0E: "#a78bfa",
      base0F: "#c4b5fd"
    },
    effects: {
      glow: true,
      glowIntensity: 0.10,
      glowColor: "#ffd700",
      particles: {
        enabled: true,
        type: "stars",
        count: 25,
        color: "#ffffff30",
        speed: 0.002
      }
    }
  }
];

// =============================================================================
// ALL PRESETS
// =============================================================================

export const ALL_PRESETS: ThemePreset[] = [
  ...LUXURY_PRESETS,
  ...GLASS_PRESETS,
  ...BENTO_PRESETS,
  ...NEUMORPHISM_PRESETS,
  ...RESPONSIVE_PRESETS,
  ...EASTER_EGG_PRESETS
];

// =============================================================================
// PRESET UTILITIES
// =============================================================================

export function getPresetsByCategory(category: ThemePreset["category"]): ThemePreset[] {
  return ALL_PRESETS.filter(p => p.category === category);
}

export function getPresetById(id: string): ThemePreset | undefined {
  return ALL_PRESETS.find(p => p.id === id);
}

export function presetToConfig(preset: ThemePreset): ThemeConfig {
  return {
    baseColor: preset.baseColor,
    heroColor: preset.heroColor,
    monitorType: preset.monitorType,
    blackBalance: preset.blackBalance,
    mode: preset.mode
  };
}

export function presetToVariant(preset: ThemePreset): ThemeVariant {
  return {
    name: preset.id,
    backgroundLightness: preset.blackBalance,
    colors: preset.palette
  };
}

/**
 * Generate HTML for the preset gallery
 */
export function generatePresetGalleryHTML(presets: ThemePreset[]): string {
  return presets.map(preset => `
    <div class="preset-card" data-preset-id="${preset.id}" style="--glow-color: ${preset.effects?.glowColor || 'transparent'}">
      <div class="preset-preview" style="background: ${preset.palette.base00}">
        <div class="preview-code">
          <span style="color: ${preset.palette.base03}">// ${preset.name}</span><br>
          <span style="color: ${preset.palette.base0E}">const</span> 
          <span style="color: ${preset.palette.base05}">theme</span> = 
          <span style="color: ${preset.palette.base0B}">"${preset.id}"</span>;
        </div>
        ${preset.effects?.glow ? `<div class="preset-glow" style="background: ${preset.effects.glowColor}"></div>` : ''}
      </div>
      <div class="preset-info">
        <div class="preset-name">${preset.name}</div>
        <div class="preset-inspiration">${preset.inspiration}</div>
        <div class="preset-tags">
          ${preset.tags.map(t => `<span class="tag">${t}</span>`).join('')}
        </div>
      </div>
    </div>
  `).join('\n');
}
