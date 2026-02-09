#!/usr/bin/env node
/**
 * Prism to OpenCode Theme Converter
 * 
 * Converts Prism Base16 presets to OpenCode's JSON theme format
 */

import * as fs from 'fs';
import * as path from 'path';

interface PrismPreset {
  id: string;
  name: string;
  category: string;
  inspiration: string;
  mode: 'dark' | 'light';
  palette: {
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
  };
  effects?: {
    glow?: boolean;
    glowColor?: string;
    glowIntensity?: number;
    particles?: {
      type: string;
      count: number;
      speed: number;
    };
  };
}

interface OpenCodeTheme {
  $schema: string;
  name: string;
  description: string;
  author: string;
  version: string;
  type: 'dark' | 'light';
  colors: {
    background: string;
    backgroundSecondary: string;
    backgroundTertiary: string;
    text: string;
    textMuted: string;
    textSubtle: string;
    border: string;
    borderMuted: string;
    borderFocus: string;
    accent: string;
    accentMuted: string;
    accentText: string;
    error: string;
    errorMuted: string;
    warning: string;
    warningMuted: string;
    success: string;
    successMuted: string;
    info: string;
    infoMuted: string;
    selection: string;
    selectionText: string;
    highlight: string;
    link: string;
    linkHover: string;
    scrollbar: string;
    scrollbarHover: string;
    syntax: {
      comment: string;
      keyword: string;
      function: string;
      string: string;
      number: string;
      type: string;
      variable: string;
      constant: string;
      operator: string;
      punctuation: string;
      tag: string;
      attribute: string;
      property: string;
      class: string;
      regex: string;
      escape: string;
    };
    diff: {
      added: string;
      addedBackground: string;
      removed: string;
      removedBackground: string;
      modified: string;
      modifiedBackground: string;
    };
    markdown: {
      heading: string;
      bold: string;
      italic: string;
      code: string;
      codeBackground: string;
      blockquote: string;
      list: string;
      link: string;
      image: string;
    };
    terminal: {
      black: string;
      red: string;
      green: string;
      yellow: string;
      blue: string;
      magenta: string;
      cyan: string;
      white: string;
      brightBlack: string;
      brightRed: string;
      brightGreen: string;
      brightYellow: string;
      brightBlue: string;
      brightMagenta: string;
      brightCyan: string;
      brightWhite: string;
    };
  };
  ui: {
    borderRadius: string;
    panelShadow: string;
    glowColor?: string;
    glowIntensity?: number;
  };
  _prism: {
    category: string;
    inspiration: string;
    heroColor: string;
    effects?: object;
  };
}

// Helper to blend colors for muted variants
function blendWithBackground(color: string, bg: string, alpha: number): string {
  const hexToRgb = (hex: string) => {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result ? {
      r: parseInt(result[1], 16),
      g: parseInt(result[2], 16),
      b: parseInt(result[3], 16)
    } : { r: 0, g: 0, b: 0 };
  };
  
  const fg = hexToRgb(color);
  const bgColor = hexToRgb(bg);
  
  const blend = (f: number, b: number) => Math.round(f * alpha + b * (1 - alpha));
  
  const r = blend(fg.r, bgColor.r).toString(16).padStart(2, '0');
  const g = blend(fg.g, bgColor.g).toString(16).padStart(2, '0');
  const b = blend(fg.b, bgColor.b).toString(16).padStart(2, '0');
  
  return `#${r}${g}${b}`;
}

function convertPreset(preset: PrismPreset): OpenCodeTheme {
  const p = preset.palette;
  const isDark = preset.mode === 'dark';
  
  return {
    $schema: "https://opencode.ai/schemas/theme.json",
    name: `Prism ${preset.name}`,
    description: preset.inspiration,
    author: "Weyl AI",
    version: "1.0.0",
    type: preset.mode,
    
    colors: {
      // Backgrounds
      background: p.base00,
      backgroundSecondary: p.base01,
      backgroundTertiary: p.base02,
      
      // Text
      text: p.base05,
      textMuted: p.base04,
      textSubtle: p.base03,
      
      // Borders
      border: p.base02,
      borderMuted: p.base01,
      borderFocus: p.base0A,
      
      // Accent (Hero color!)
      accent: p.base0A,
      accentMuted: p.base0F,
      accentText: p.base00,
      
      // Semantic colors
      error: p.base08,
      errorMuted: blendWithBackground(p.base08, p.base00, 0.2),
      warning: p.base09,
      warningMuted: blendWithBackground(p.base09, p.base00, 0.2),
      success: p.base0B,
      successMuted: blendWithBackground(p.base0B, p.base00, 0.2),
      info: p.base0D,
      infoMuted: blendWithBackground(p.base0D, p.base00, 0.2),
      
      // Selection
      selection: p.base02,
      selectionText: p.base05,
      highlight: `${p.base0A}30`,
      
      // Links
      link: p.base0C,
      linkHover: p.base0A,
      
      // Scrollbar
      scrollbar: p.base03,
      scrollbarHover: p.base04,
      
      // Syntax highlighting
      syntax: {
        comment: p.base03,
        keyword: p.base0E,
        function: p.base0D,
        string: p.base0B,
        number: p.base09,
        type: p.base0A,      // HERO COLOR for types!
        variable: p.base05,
        constant: p.base09,
        operator: p.base05,
        punctuation: p.base04,
        tag: p.base08,
        attribute: p.base0A,
        property: p.base05,
        class: p.base0A,     // HERO COLOR for classes!
        regex: p.base0C,
        escape: p.base0C
      },
      
      // Diff
      diff: {
        added: p.base0B,
        addedBackground: blendWithBackground(p.base0B, p.base00, 0.15),
        removed: p.base08,
        removedBackground: blendWithBackground(p.base08, p.base00, 0.15),
        modified: p.base0D,
        modifiedBackground: blendWithBackground(p.base0D, p.base00, 0.15)
      },
      
      // Markdown
      markdown: {
        heading: p.base0D,
        bold: p.base05,
        italic: p.base0E,
        code: p.base0B,
        codeBackground: p.base01,
        blockquote: p.base04,
        list: p.base0A,
        link: p.base0C,
        image: p.base0D
      },
      
      // Terminal ANSI colors
      terminal: {
        black: p.base00,
        red: p.base08,
        green: p.base0B,
        yellow: p.base0A,
        blue: p.base0D,
        magenta: p.base0E,
        cyan: p.base0C,
        white: p.base05,
        brightBlack: p.base03,
        brightRed: p.base08,
        brightGreen: p.base0B,
        brightYellow: p.base0A,
        brightBlue: p.base0D,
        brightMagenta: p.base0E,
        brightCyan: p.base0C,
        brightWhite: p.base07
      }
    },
    
    ui: {
      borderRadius: preset.category === 'bento' ? '12px' : '8px',
      panelShadow: `0 8px 32px rgba(0,0,0,${isDark ? '0.4' : '0.1'})`,
      ...(preset.effects?.glowColor && { glowColor: preset.effects.glowColor }),
      ...(preset.effects?.glowIntensity && { glowIntensity: preset.effects.glowIntensity })
    },
    
    _prism: {
      category: preset.category,
      inspiration: preset.inspiration,
      heroColor: p.base0A,
      ...(preset.effects && { effects: preset.effects })
    }
  };
}

// All Prism presets
const PRESETS: PrismPreset[] = [
  {
    id: "nero_marquina",
    name: "Nero Marquina",
    category: "luxury",
    inspiration: "Black Spanish marble with gold veining",
    mode: "dark",
    palette: {
      base00: "#08080a", base01: "#101014", base02: "#18181e", base03: "#3a3a45",
      base04: "#5a5a68", base05: "#e8e4dc", base06: "#f5f2ea", base07: "#fffef8",
      base08: "#e85454", base09: "#e8a054", base0A: "#d4af37", base0B: "#54c878",
      base0C: "#54b4b8", base0D: "#5494e8", base0E: "#b454e8", base0F: "#a89050"
    },
    effects: { glow: true, glowColor: "#d4af37", glowIntensity: 0.08 }
  },
  {
    id: "obsidian_rose_gold",
    name: "Obsidian Rose Gold",
    category: "luxury",
    inspiration: "Volcanic glass with rose gold veining",
    mode: "dark",
    palette: {
      base00: "#050404", base01: "#0c0a0a", base02: "#141210", base03: "#3a3535",
      base04: "#5a5555", base05: "#f0e8e8", base06: "#f8f2f2", base07: "#fffafa",
      base08: "#e87878", base09: "#e8a878", base0A: "#e8b4b8", base0B: "#78c8a8",
      base0C: "#78b8c8", base0D: "#7898e8", base0E: "#c878e8", base0F: "#a88878"
    },
    effects: { glow: true, glowColor: "#e8b4b8", glowIntensity: 0.06 }
  },
  {
    id: "midnight_sapphire",
    name: "Midnight Sapphire",
    category: "luxury",
    inspiration: "Deep blue gemstone with platinum glow",
    mode: "dark",
    palette: {
      base00: "#050810", base01: "#0a1018", base02: "#101825", base03: "#2a3548",
      base04: "#4a5568", base05: "#e0e8f8", base06: "#f0f4ff", base07: "#fafcff",
      base08: "#f87171", base09: "#fb923c", base0A: "#c0c0d0", base0B: "#6ee7b7",
      base0C: "#67e8f9", base0D: "#60a5fa", base0E: "#a78bfa", base0F: "#8090a0"
    },
    effects: { glow: true, glowColor: "#60a5fa", glowIntensity: 0.12 }
  },
  {
    id: "emerald_velvet",
    name: "Emerald Velvet",
    category: "luxury",
    inspiration: "Rich emerald on black velvet with gold filigree",
    mode: "dark",
    palette: {
      base00: "#040806", base01: "#081008", base02: "#101810", base03: "#283828",
      base04: "#485848", base05: "#e0f0e0", base06: "#f0fff0", base07: "#f8fff8",
      base08: "#f87171", base09: "#d4af37", base0A: "#d4af37", base0B: "#50c878",
      base0C: "#5fd4b8", base0D: "#60a5fa", base0E: "#a78bfa", base0F: "#8fa878"
    },
    effects: { glow: true, glowColor: "#50c878", glowIntensity: 0.10 }
  },
  {
    id: "aurora_glass",
    name: "Aurora Glass",
    category: "glass",
    inspiration: "Northern lights through frosted ice panels",
    mode: "dark",
    palette: {
      base00: "#0a0815", base01: "#12101f", base02: "#1a1828", base03: "#3a3550",
      base04: "#5a5570", base05: "#e8f0f8", base06: "#f0f8ff", base07: "#faffff",
      base08: "#f87171", base09: "#fb923c", base0A: "#a78bfa", base0B: "#4ade80",
      base0C: "#22d3ee", base0D: "#60a5fa", base0E: "#c084fc", base0F: "#64ffda"
    },
    effects: { glow: true, glowColor: "#64ffda", glowIntensity: 0.06 }
  },
  {
    id: "tokyo_night_bento",
    name: "Tokyo Night Bento",
    category: "bento",
    inspiration: "Japanese minimalism meets neon cityscape",
    mode: "dark",
    palette: {
      base00: "#0f0f18", base01: "#16161f", base02: "#1e1e28", base03: "#3a3a4a",
      base04: "#5a5a6a", base05: "#e8e8f0", base06: "#f0f0f8", base07: "#fafaff",
      base08: "#f7768e", base09: "#ff9e64", base0A: "#e0af68", base0B: "#9ece6a",
      base0C: "#73daca", base0D: "#7aa2f7", base0E: "#bb9af7", base0F: "#c792ea"
    },
    effects: { glow: true, glowColor: "#bb9af7", glowIntensity: 0.10 }
  },
  {
    id: "ember_hearth",
    name: "Ember Hearth",
    category: "responsive",
    inspiration: "Warm fireplace with embers responding to activity",
    mode: "dark",
    palette: {
      base00: "#0c0908", base01: "#141010", base02: "#1c1614", base03: "#3a302a",
      base04: "#5a4a40", base05: "#f8f0e0", base06: "#fff8e8", base07: "#fffff0",
      base08: "#ff6b6b", base09: "#ffa94d", base0A: "#ffd93d", base0B: "#6bcb77",
      base0C: "#4d96ff", base0D: "#ff8c42", base0E: "#c792ea", base0F: "#ffb347"
    },
    effects: { 
      glow: true, 
      glowColor: "#ff6b35", 
      glowIntensity: 0.14,
      particles: { type: "embers", count: 4, speed: 0.1 }
    }
  },
  {
    id: "tide_pool",
    name: "Tide Pool",
    category: "responsive",
    inspiration: "Bioluminescent creatures responding to movement",
    mode: "dark",
    palette: {
      base00: "#06090c", base01: "#0c1218", base02: "#121a20", base03: "#283540",
      base04: "#485560", base05: "#e0f0f8", base06: "#f0faff", base07: "#f8ffff",
      base08: "#f87171", base09: "#fb923c", base0A: "#40e0d0", base0B: "#00ff88",
      base0C: "#00d4ff", base0D: "#40e0d0", base0E: "#a78bfa", base0F: "#64ffda"
    },
    effects: { 
      glow: true, 
      glowColor: "#40e0d0", 
      glowIntensity: 0.14,
      particles: { type: "bioluminescent", count: 5, speed: 0.05 }
    }
  },
  {
    id: "constellation_map",
    name: "Constellation Map",
    category: "easter_eggs",
    inspiration: "Star charts with connections forming over time",
    mode: "dark",
    palette: {
      base00: "#050608", base01: "#0a0c10", base02: "#10141a", base03: "#283040",
      base04: "#485060", base05: "#e8f0ff", base06: "#f0f8ff", base07: "#fafeff",
      base08: "#f87171", base09: "#fbbf24", base0A: "#ffd700", base0B: "#4ade80",
      base0C: "#22d3ee", base0D: "#60a5fa", base0E: "#a78bfa", base0F: "#c4b5fd"
    },
    effects: { 
      glow: true, 
      glowColor: "#ffd700", 
      glowIntensity: 0.10,
      particles: { type: "stars", count: 25, speed: 0.002 }
    }
  },
  {
    id: "porcelain_moon",
    name: "Porcelain Moon",
    category: "neumorphism",
    inspiration: "Fine bone china in soft moonlight",
    mode: "light",
    palette: {
      base00: "#e8eaee", base01: "#e8eaee", base02: "#dfe1e5", base03: "#a0a4aa",
      base04: "#707478", base05: "#1a1c20", base06: "#101214", base07: "#050608",
      base08: "#dc2626", base09: "#ea580c", base0A: "#ca8a04", base0B: "#16a34a",
      base0C: "#0891b2", base0D: "#2563eb", base0E: "#7c3aed", base0F: "#6b7280"
    }
  }
];

// Generate all themes
function generateAll(outputDir: string) {
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }
  
  for (const preset of PRESETS) {
    const theme = convertPreset(preset);
    const filename = preset.id.replace(/_/g, '-') + '.json';
    const filepath = path.join(outputDir, filename);
    fs.writeFileSync(filepath, JSON.stringify(theme, null, 2));
    console.log(`✓ Generated ${filename}`);
  }
  
  console.log(`\n✨ Generated ${PRESETS.length} themes in ${outputDir}`);
}

// Run if executed directly
const outputDir = process.argv[2] || './themes';
generateAll(outputDir);
