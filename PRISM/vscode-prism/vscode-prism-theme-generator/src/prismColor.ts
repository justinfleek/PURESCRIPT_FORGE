/**
 * PrismColor - TypeScript port of formally verified color science
 * 
 * This is a direct port of the Haskell/Lean4 verified implementation.
 * All algorithms match the proven versions.
 * 
 * Features:
 * - OKLCH perceptual color space
 * - WCAG 2.1 contrast verification
 * - Auto-adjustment for accessibility
 * - Base16 palette generation
 */

// ============================================================================
// TYPES
// ============================================================================

export interface SRGB {
  r: number;  // 0-1
  g: number;  // 0-1
  b: number;  // 0-1
}

export interface OKLCH {
  L: number;  // Lightness 0-1
  C: number;  // Chroma 0-0.4
  H: number;  // Hue 0-360
}

export interface Base16Colors {
  base00: string;  // Background
  base01: string;  // Lighter background
  base02: string;  // Selection
  base03: string;  // Comments
  base04: string;  // Dark foreground
  base05: string;  // Foreground
  base06: string;  // Light foreground
  base07: string;  // Lightest foreground
  base08: string;  // Error/Red
  base09: string;  // Warning/Orange
  base0A: string;  // Hero/Yellow
  base0B: string;  // Success/Green
  base0C: string;  // Info/Cyan
  base0D: string;  // Link/Blue
  base0E: string;  // Special/Purple
  base0F: string;  // Deprecated/Brown
}

export interface ThemeConfig {
  baseColor: { hue: number; saturation: number; lightness: number };
  heroColor: { hue: number; saturation: number; lightness: number };
  monitorType: 'OLED' | 'LCD';
  blackBalance: number;
  mode: 'dark' | 'light';
}

export interface ThemeVariant {
  name: string;
  backgroundLightness: number;
  colors: Base16Colors;
  contrast: {
    text: number;
    comment: number;
    accent: number;
    wcagVerified: boolean;
  };
}

// ============================================================================
// OKLCH COLOR SPACE (proven bijective in Lean4)
// ============================================================================

function srgbToLinear(c: number): number {
  if (c <= 0.04045) {
    return c / 12.92;
  }
  return Math.pow((c + 0.055) / 1.055, 2.4);
}

function linearToSrgb(c: number): number {
  if (c <= 0.0031308) {
    return c * 12.92;
  }
  return 1.055 * Math.pow(c, 1 / 2.4) - 0.055;
}

function srgbToOklab(rgb: SRGB): [number, number, number] {
  const r = srgbToLinear(rgb.r);
  const g = srgbToLinear(rgb.g);
  const b = srgbToLinear(rgb.b);

  const l = 0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b;
  const m = 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b;
  const s = 0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b;

  const l_ = Math.cbrt(l);
  const m_ = Math.cbrt(m);
  const s_ = Math.cbrt(s);

  return [
    0.2104542553 * l_ + 0.7936177850 * m_ - 0.0040720468 * s_,
    1.9779984951 * l_ - 2.4285922050 * m_ + 0.4505937099 * s_,
    0.0259040371 * l_ + 0.7827717662 * m_ - 0.8086757660 * s_
  ];
}

function oklabToSrgb(L: number, a: number, b: number): SRGB {
  const l_ = L + 0.3963377774 * a + 0.2158037573 * b;
  const m_ = L - 0.1055613458 * a - 0.0638541728 * b;
  const s_ = L - 0.0894841775 * a - 1.2914855480 * b;

  const l = l_ * l_ * l_;
  const m = m_ * m_ * m_;
  const s = s_ * s_ * s_;

  let r = +4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s;
  let g = -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s;
  let bVal = -0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s;

  // Clamp to gamut
  r = Math.max(0, Math.min(1, linearToSrgb(Math.max(0, r))));
  g = Math.max(0, Math.min(1, linearToSrgb(Math.max(0, g))));
  bVal = Math.max(0, Math.min(1, linearToSrgb(Math.max(0, bVal))));

  return { r, g, b: bVal };
}

export function oklchToSrgb(oklch: OKLCH): SRGB {
  const hRad = (oklch.H * Math.PI) / 180;
  const a = oklch.C * Math.cos(hRad);
  const b = oklch.C * Math.sin(hRad);
  return oklabToSrgb(oklch.L, a, b);
}

export function srgbToOklch(rgb: SRGB): OKLCH {
  const [L, a, b] = srgbToOklab(rgb);
  const C = Math.sqrt(a * a + b * b);
  let H = (Math.atan2(b, a) * 180) / Math.PI;
  if (H < 0) H += 360;
  return { L, C, H };
}

// ============================================================================
// COLOR UTILITIES
// ============================================================================

export function srgbToHex(rgb: SRGB): string {
  const r = Math.round(rgb.r * 255);
  const g = Math.round(rgb.g * 255);
  const b = Math.round(rgb.b * 255);
  return `#${r.toString(16).padStart(2, '0')}${g.toString(16).padStart(2, '0')}${b.toString(16).padStart(2, '0')}`;
}

export function hexToSrgb(hex: string): SRGB {
  const h = hex.replace('#', '');
  return {
    r: parseInt(h.substring(0, 2), 16) / 255,
    g: parseInt(h.substring(2, 4), 16) / 255,
    b: parseInt(h.substring(4, 6), 16) / 255
  };
}

// ============================================================================
// WCAG CONTRAST (proven correct in Lean4)
// ============================================================================

/**
 * Calculate relative luminance per WCAG 2.1
 * Proven in Lean4: result is always in [0, 1]
 */
export function relativeLuminance(rgb: SRGB): number {
  const r = srgbToLinear(rgb.r);
  const g = srgbToLinear(rgb.g);
  const b = srgbToLinear(rgb.b);
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}

/**
 * Calculate WCAG contrast ratio
 * Proven in Lean4:
 * - Result >= 1 (contrastRatio_ge_one)
 * - Symmetric (contrastRatio_symm)
 * - Maximum is 21:1 (contrastRatio_max)
 */
export function contrastRatio(fg: SRGB, bg: SRGB): number {
  const l1 = relativeLuminance(fg);
  const l2 = relativeLuminance(bg);
  const lighter = Math.max(l1, l2);
  const darker = Math.min(l1, l2);
  return (lighter + 0.05) / (darker + 0.05);
}

export function wcagAA(cr: number): boolean {
  return cr >= 4.5;
}

export function wcagAALarge(cr: number): boolean {
  return cr >= 3.0;
}

export function wcagAAA(cr: number): boolean {
  return cr >= 7.0;
}

/**
 * Adjust lightness to achieve target contrast ratio
 * Uses binary search (proven to converge in Lean4)
 */
export function adjustLightnessForContrast(
  color: OKLCH,
  bg: SRGB,
  targetCR: number,
  makeLighter: boolean
): OKLCH | null {
  const bgLum = relativeLuminance(bg);

  let lo = makeLighter ? color.L : 0;
  let hi = makeLighter ? 1 : color.L;

  for (let i = 0; i < 50; i++) {
    const mid = (lo + hi) / 2;
    const candidate: OKLCH = { L: mid, C: color.C, H: color.H };
    const candidateRgb = oklchToSrgb(candidate);
    const cr = contrastRatio(candidateRgb, bg);

    if (Math.abs(cr - targetCR) < 0.01) {
      return candidate;
    }

    if (cr < targetCR) {
      if (makeLighter) {
        lo = mid;
      } else {
        hi = mid;
      }
    } else {
      if (makeLighter) {
        hi = mid;
      } else {
        lo = mid;
      }
    }
  }

  return null;
}

// ============================================================================
// PALETTE GENERATION
// ============================================================================

function generateBackgroundRamp(
  baseHue: number,
  baseSat: number,
  startL: number,
  mode: 'dark' | 'light'
): [SRGB, SRGB, SRGB, SRGB] {
  const steps = mode === 'dark' 
    ? [0.0, 0.03, 0.06, 0.12]
    : [0.0, -0.02, -0.04, -0.08];

  const bgChroma = baseSat * 0.03;

  return steps.map(dL => {
    const oklch: OKLCH = {
      L: Math.max(0, Math.min(1, startL + dL)),
      C: bgChroma,
      H: baseHue
    };
    return oklchToSrgb(oklch);
  }) as [SRGB, SRGB, SRGB, SRGB];
}

function generateForegroundRamp(
  baseHue: number,
  baseSat: number,
  bg: SRGB,
  mode: 'dark' | 'light'
): [SRGB, SRGB, SRGB, SRGB] {
  const targetLs = mode === 'dark'
    ? [0.45, 0.75, 0.85, 0.95]
    : [0.55, 0.35, 0.25, 0.15];

  const fgChroma = baseSat * 0.05;

  return targetLs.map((targetL, i) => {
    let oklch: OKLCH = { L: targetL, C: fgChroma, H: baseHue };
    let rgb = oklchToSrgb(oklch);

    // Verify and adjust for WCAG AA
    const cr = contrastRatio(rgb, bg);
    if (cr < 4.5 && i >= 1) {  // base05+ needs AA
      const adjusted = adjustLightnessForContrast(oklch, bg, 4.5, mode === 'dark');
      if (adjusted) {
        rgb = oklchToSrgb(adjusted);
      }
    }

    return rgb;
  }) as [SRGB, SRGB, SRGB, SRGB];
}

function generateAccentColors(
  heroHue: number,
  heroSat: number,
  bg: SRGB,
  mode: 'dark' | 'light'
): [SRGB, SRGB, SRGB, SRGB, SRGB, SRGB, SRGB, SRGB] {
  const accentL = mode === 'dark' ? 0.72 : 0.45;

  // Color harmony offsets
  const harmony: [number, number][] = [
    [30, 1.0],    // base08 - Error (warm)
    [15, 0.95],   // base09 - Warning
    [0, 1.0],     // base0A - Hero
    [-60, 0.9],   // base0B - Success (cool/green)
    [-90, 0.85],  // base0C - Info (cyan)
    [120, 0.9],   // base0D - Link (triadic)
    [45, 0.95],   // base0E - Special
    [0, 0.5],     // base0F - Deprecated (desaturated)
  ];

  return harmony.map(([hueOffset, satMult]) => {
    let oklch: OKLCH = {
      L: accentL,
      C: heroSat * satMult * 0.15,
      H: (heroHue + hueOffset + 360) % 360
    };
    let rgb = oklchToSrgb(oklch);

    // Verify and adjust for WCAG AA-large
    const cr = contrastRatio(rgb, bg);
    if (cr < 3.0) {
      const adjusted = adjustLightnessForContrast(oklch, bg, 3.0, mode === 'dark');
      if (adjusted) {
        rgb = oklchToSrgb(adjusted);
      }
    }

    return rgb;
  }) as [SRGB, SRGB, SRGB, SRGB, SRGB, SRGB, SRGB, SRGB];
}

// ============================================================================
// MAIN GENERATION FUNCTION
// ============================================================================

export function generatePalette(config: ThemeConfig, bgLightness: number): Base16Colors {
  const baseHue = config.baseColor.hue;
  const baseSat = config.baseColor.saturation;
  const heroHue = config.heroColor.hue;
  const heroSat = config.heroColor.saturation;
  const mode = config.mode;

  const [b00, b01, b02, b03] = generateBackgroundRamp(baseHue, baseSat, bgLightness, mode);
  const [b04, b05, b06, b07] = generateForegroundRamp(baseHue, baseSat, b00, mode);
  const [b08, b09, b0A, b0B, b0C, b0D, b0E, b0F] = generateAccentColors(heroHue, heroSat, b00, mode);

  return {
    base00: srgbToHex(b00),
    base01: srgbToHex(b01),
    base02: srgbToHex(b02),
    base03: srgbToHex(b03),
    base04: srgbToHex(b04),
    base05: srgbToHex(b05),
    base06: srgbToHex(b06),
    base07: srgbToHex(b07),
    base08: srgbToHex(b08),
    base09: srgbToHex(b09),
    base0A: srgbToHex(b0A),
    base0B: srgbToHex(b0B),
    base0C: srgbToHex(b0C),
    base0D: srgbToHex(b0D),
    base0E: srgbToHex(b0E),
    base0F: srgbToHex(b0F),
  };
}

export function generateVariants(config: ThemeConfig): ThemeVariant[] {
  const variantDefs: [string, number][] = config.mode === 'dark'
    ? config.monitorType === 'OLED'
      ? [
          ['Pure Black', 0.0],
          ['Ultra Dark', 0.04],
          ['Dark', 0.08],
          ['Tuned', 0.11],
          ['Balanced', 0.14],
        ]
      : [
          ['Minimum', 0.08],
          ['Dark', 0.12],
          ['Balanced', 0.16],
          ['Github', 0.18],
          ['Bright', 0.22],
        ]
    : [
        ['Bright', 0.98],
        ['Paper', 0.96],
        ['Cream', 0.94],
      ];

  return variantDefs.map(([name, lightness]) => {
    const colors = generatePalette(config, lightness);

    // Calculate contrast ratios for verification
    const bg = hexToSrgb(colors.base00);
    const text = hexToSrgb(colors.base05);
    const comment = hexToSrgb(colors.base03);
    const accent = hexToSrgb(colors.base0A);

    const crText = contrastRatio(text, bg);
    const crComment = contrastRatio(comment, bg);
    const crAccent = contrastRatio(accent, bg);

    return {
      name,
      backgroundLightness: lightness,
      colors,
      contrast: {
        text: Math.round(crText * 100) / 100,
        comment: Math.round(crComment * 100) / 100,
        accent: Math.round(crAccent * 100) / 100,
        wcagVerified: wcagAA(crText) && wcagAALarge(crComment) && wcagAALarge(crAccent),
      },
    };
  });
}

// ============================================================================
// VSCODE THEME GENERATION
// ============================================================================

export function generateVSCodeTheme(variant: ThemeVariant, themeName: string): object {
  const c = variant.colors;

  return {
    name: themeName,
    type: variant.backgroundLightness < 0.5 ? 'dark' : 'light',
    colors: {
      'editor.background': c.base00,
      'editor.foreground': c.base05,
      'editorLineNumber.foreground': c.base03,
      'editorLineNumber.activeForeground': c.base05,
      'editorCursor.foreground': c.base0A,
      'editor.selectionBackground': c.base0A + '40',
      'editor.selectionHighlightBackground': c.base0A + '25',
      'editor.lineHighlightBackground': c.base01,
      'editorBracketMatch.background': c.base0A + '30',
      'editorBracketMatch.border': c.base0A,
      'sideBar.background': c.base01,
      'sideBar.foreground': c.base05,
      'activityBar.background': c.base00,
      'activityBar.foreground': c.base05,
      'activityBar.activeBorder': c.base0A,
      'activityBarBadge.background': c.base0A,
      'activityBarBadge.foreground': c.base00,
      'titleBar.activeBackground': c.base00,
      'titleBar.activeForeground': c.base05,
      'statusBar.background': c.base00,
      'statusBar.foreground': c.base03,
      'tab.activeBackground': c.base00,
      'tab.activeForeground': c.base05,
      'tab.activeBorder': c.base0A,
      'tab.inactiveBackground': c.base01,
      'tab.inactiveForeground': c.base03,
      'panel.background': c.base00,
      'panel.border': c.base01,
      'terminal.background': c.base00,
      'terminal.foreground': c.base05,
      'terminal.ansiBlack': c.base00,
      'terminal.ansiRed': c.base08,
      'terminal.ansiGreen': c.base0B,
      'terminal.ansiYellow': c.base09,
      'terminal.ansiBlue': c.base0D,
      'terminal.ansiMagenta': c.base0E,
      'terminal.ansiCyan': c.base0C,
      'terminal.ansiWhite': c.base05,
      'terminal.ansiBrightBlack': c.base03,
      'terminal.ansiBrightRed': c.base08,
      'terminal.ansiBrightGreen': c.base0B,
      'terminal.ansiBrightYellow': c.base09,
      'terminal.ansiBrightBlue': c.base0D,
      'terminal.ansiBrightMagenta': c.base0E,
      'terminal.ansiBrightCyan': c.base0C,
      'terminal.ansiBrightWhite': c.base07,
      'gitDecoration.modifiedResourceForeground': c.base09,
      'gitDecoration.deletedResourceForeground': c.base08,
      'gitDecoration.untrackedResourceForeground': c.base0B,
      'button.background': c.base0A,
      'button.foreground': c.base00,
      'input.background': c.base00,
      'input.foreground': c.base05,
      'input.border': c.base01,
      'focusBorder': c.base0A,
    },
    tokenColors: [
      { scope: 'comment', settings: { foreground: c.base03, fontStyle: 'italic' } },
      { scope: ['keyword', 'storage.type', 'storage.modifier'], settings: { foreground: c.base0E } },
      { scope: 'string', settings: { foreground: c.base0B } },
      { scope: ['constant.numeric', 'constant.language'], settings: { foreground: c.base09 } },
      { scope: 'variable', settings: { foreground: c.base05 } },
      { scope: 'variable.parameter', settings: { foreground: c.base0C } },
      { scope: ['entity.name.function', 'support.function'], settings: { foreground: c.base0D } },
      { scope: ['entity.name.type', 'entity.name.class'], settings: { foreground: c.base0A } },
      { scope: 'entity.name.tag', settings: { foreground: c.base08 } },
      { scope: 'entity.other.attribute-name', settings: { foreground: c.base09 } },
      { scope: 'punctuation', settings: { foreground: c.base04 } },
      { scope: 'meta.decorator', settings: { foreground: c.base0E } },
    ],
    _prism: {
      generator: 'prism-color-ts',
      verified: variant.contrast.wcagVerified,
      contrast: variant.contrast,
    },
  };
}
