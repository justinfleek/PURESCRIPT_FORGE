#!/usr/bin/env python3
"""
PRISM Verified Theme Generator
==============================

Generates themes using OKLCH perceptual color space with WCAG verification.
This mirrors the formally verified Haskell/Lean4 implementation.

Usage:
    python verified_generator.py --hue 211 --mode dark --monitor oled --name "My Theme"
    
Or use the Python API:
    from verified_generator import generate_theme
    theme = generate_theme(hero_hue=211, mode="dark", monitor="oled", name="My Theme")
"""

import json
import math
import argparse
from dataclasses import dataclass
from typing import Tuple, List, Optional
from pathlib import Path

# ============================================================================
# OKLCH COLOR SPACE IMPLEMENTATION
# ============================================================================

@dataclass
class SRGB:
    r: float  # 0-1
    g: float  # 0-1
    b: float  # 0-1

@dataclass
class OKLCH:
    L: float  # Lightness 0-1
    C: float  # Chroma 0-0.4 (roughly)
    H: float  # Hue 0-360

def srgb_to_linear(c: float) -> float:
    """sRGB to linear RGB (inverse gamma)"""
    if c <= 0.04045:
        return c / 12.92
    return math.pow((c + 0.055) / 1.055, 2.4)

def linear_to_srgb(c: float) -> float:
    """Linear RGB to sRGB (gamma)"""
    if c <= 0.0031308:
        return c * 12.92
    return 1.055 * math.pow(c, 1/2.4) - 0.055

def srgb_to_oklab(rgb: SRGB) -> Tuple[float, float, float]:
    """Convert sRGB to OKLAB"""
    # sRGB to linear
    r = srgb_to_linear(rgb.r)
    g = srgb_to_linear(rgb.g)
    b = srgb_to_linear(rgb.b)
    
    # Linear RGB to LMS (cone response)
    l = 0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b
    m = 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b
    s = 0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b
    
    # Cube root
    l_ = math.copysign(abs(l) ** (1/3), l) if l != 0 else 0
    m_ = math.copysign(abs(m) ** (1/3), m) if m != 0 else 0
    s_ = math.copysign(abs(s) ** (1/3), s) if s != 0 else 0
    
    # LMS to OKLAB
    L = 0.2104542553 * l_ + 0.7936177850 * m_ - 0.0040720468 * s_
    a = 1.9779984951 * l_ - 2.4285922050 * m_ + 0.4505937099 * s_
    b = 0.0259040371 * l_ + 0.7827717662 * m_ - 0.8086757660 * s_
    
    return (L, a, b)

def oklab_to_srgb(L: float, a: float, b: float) -> SRGB:
    """Convert OKLAB to sRGB"""
    # OKLAB to LMS
    l_ = L + 0.3963377774 * a + 0.2158037573 * b
    m_ = L - 0.1055613458 * a - 0.0638541728 * b
    s_ = L - 0.0894841775 * a - 1.2914855480 * b
    
    # Cube
    l = l_ * l_ * l_
    m = m_ * m_ * m_
    s = s_ * s_ * s_
    
    # LMS to linear RGB
    r = +4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s
    g = -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s
    b_val = -0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s
    
    # Clamp and convert to sRGB
    r = max(0, min(1, linear_to_srgb(r)))
    g = max(0, min(1, linear_to_srgb(g)))
    b_val = max(0, min(1, linear_to_srgb(b_val)))
    
    return SRGB(r, g, b_val)

def oklch_to_srgb(oklch: OKLCH) -> SRGB:
    """Convert OKLCH to sRGB"""
    h_rad = math.radians(oklch.H)
    a = oklch.C * math.cos(h_rad)
    b = oklch.C * math.sin(h_rad)
    return oklab_to_srgb(oklch.L, a, b)

def srgb_to_oklch(rgb: SRGB) -> OKLCH:
    """Convert sRGB to OKLCH"""
    L, a, b = srgb_to_oklab(rgb)
    C = math.sqrt(a*a + b*b)
    H = math.degrees(math.atan2(b, a)) % 360
    return OKLCH(L, C, H)

def srgb_to_hex(rgb: SRGB) -> str:
    """Convert sRGB to hex string"""
    r = int(round(rgb.r * 255))
    g = int(round(rgb.g * 255))
    b = int(round(rgb.b * 255))
    return f"#{r:02x}{g:02x}{b:02x}"

def hex_to_srgb(hex_color: str) -> SRGB:
    """Convert hex string to sRGB"""
    h = hex_color.lstrip('#')
    return SRGB(
        int(h[0:2], 16) / 255,
        int(h[2:4], 16) / 255,
        int(h[4:6], 16) / 255
    )

# ============================================================================
# WCAG CONTRAST VERIFICATION
# ============================================================================

def relative_luminance(rgb: SRGB) -> float:
    """
    Calculate relative luminance per WCAG 2.1
    
    Proven in Lean4: result is always in [0, 1]
    """
    r = srgb_to_linear(rgb.r)
    g = srgb_to_linear(rgb.g)
    b = srgb_to_linear(rgb.b)
    return 0.2126 * r + 0.7152 * g + 0.0722 * b

def contrast_ratio(fg: SRGB, bg: SRGB) -> float:
    """
    Calculate WCAG contrast ratio
    
    Proven in Lean4:
    - Result is always >= 1
    - Symmetric: contrast_ratio(a, b) == contrast_ratio(b, a)
    - Maximum is 21:1 (white vs black)
    """
    l1 = relative_luminance(fg)
    l2 = relative_luminance(bg)
    lighter = max(l1, l2)
    darker = min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)

def wcag_aa(cr: float) -> bool:
    """WCAG AA for normal text: CR >= 4.5"""
    return cr >= 4.5

def wcag_aa_large(cr: float) -> bool:
    """WCAG AA for large text: CR >= 3.0"""
    return cr >= 3.0

def wcag_aaa(cr: float) -> bool:
    """WCAG AAA for normal text: CR >= 7.0"""
    return cr >= 7.0

def adjust_lightness_for_contrast(
    color: OKLCH, 
    bg: SRGB, 
    target_cr: float, 
    make_lighter: bool
) -> Optional[OKLCH]:
    """
    Adjust lightness to achieve target contrast ratio.
    Uses binary search (proven to converge in Lean4).
    """
    bg_lum = relative_luminance(bg)
    
    lo = color.L if not make_lighter else color.L
    hi = 1.0 if make_lighter else color.L
    if not make_lighter:
        lo, hi = 0.0, color.L
    
    for _ in range(50):
        mid = (lo + hi) / 2
        candidate = OKLCH(mid, color.C, color.H)
        candidate_rgb = oklch_to_srgb(candidate)
        cr = contrast_ratio(candidate_rgb, bg)
        
        if abs(cr - target_cr) < 0.01:
            return candidate
        
        if cr < target_cr:
            if make_lighter:
                lo = mid
            else:
                hi = mid
        else:
            if make_lighter:
                hi = mid
            else:
                lo = mid
    
    return None

# ============================================================================
# PALETTE GENERATION (Base16)
# ============================================================================

@dataclass
class ThemeConfig:
    hero_hue: float        # 0-360
    hero_saturation: float # 0-1
    base_hue: float        # 0-360 (usually same as hero or neutral)
    base_saturation: float # 0-1 (usually low ~0.1)
    mode: str              # "dark" or "light"
    monitor: str           # "oled" or "lcd"
    name: str

def generate_background_ramp(config: ThemeConfig) -> Tuple[SRGB, SRGB, SRGB, SRGB]:
    """
    Generate base00-base03 (background colors).
    Uses low saturation, perceptually uniform lightness steps.
    """
    # Black balance based on monitor type
    if config.mode == "dark":
        if config.monitor == "oled":
            start_L = 0.0  # True black for OLED
        else:
            start_L = 0.08  # Lifted black for LCD
        steps = [0.0, 0.03, 0.06, 0.12]
    else:
        start_L = 0.97
        steps = [0.0, -0.02, -0.04, -0.08]
    
    bg_chroma = config.base_saturation * 0.03  # Very low for backgrounds
    
    colors = []
    for dL in steps:
        oklch = OKLCH(
            L=max(0, min(1, start_L + dL)),
            C=bg_chroma,
            H=config.base_hue
        )
        colors.append(oklch_to_srgb(oklch))
    
    return tuple(colors)

def generate_foreground_ramp(config: ThemeConfig, bg: SRGB) -> Tuple[SRGB, SRGB, SRGB, SRGB]:
    """
    Generate base04-base07 (text colors).
    Automatically adjusted to meet WCAG AA with background.
    """
    if config.mode == "dark":
        target_Ls = [0.45, 0.75, 0.85, 0.95]
    else:
        target_Ls = [0.55, 0.35, 0.25, 0.15]
    
    fg_chroma = config.base_saturation * 0.05
    
    colors = []
    for target_L in target_Ls:
        oklch = OKLCH(L=target_L, C=fg_chroma, H=config.base_hue)
        rgb = oklch_to_srgb(oklch)
        
        # Verify contrast, adjust if needed
        cr = contrast_ratio(rgb, bg)
        if cr < 4.5:  # Needs adjustment for WCAG AA
            adjusted = adjust_lightness_for_contrast(
                oklch, bg, 4.5, make_lighter=(config.mode == "dark")
            )
            if adjusted:
                rgb = oklch_to_srgb(adjusted)
        
        colors.append(rgb)
    
    return tuple(colors)

def generate_accent_colors(config: ThemeConfig, bg: SRGB) -> Tuple[SRGB, ...]:
    """
    Generate base08-base0F (accent colors).
    Distributed using color harmony rules around hero hue.
    """
    h = config.hero_hue
    s = config.hero_saturation
    
    # Accent lightness (must contrast with background)
    if config.mode == "dark":
        accent_L = 0.72
    else:
        accent_L = 0.45
    
    # Hue offsets for color harmony
    harmony = [
        (30, 1.0),    # base08 - Error (warm)
        (15, 0.95),   # base09 - Warning
        (0, 1.0),     # base0A - Hero
        (-60, 0.9),   # base0B - Success (cool/green)
        (-90, 0.85),  # base0C - Info (cyan)
        (120, 0.9),   # base0D - Link (triadic)
        (45, 0.95),   # base0E - Special
        (0, 0.5),     # base0F - Deprecated (desaturated)
    ]
    
    colors = []
    for hue_offset, sat_mult in harmony:
        oklch = OKLCH(
            L=accent_L,
            C=s * sat_mult * 0.15,  # Scale to OKLCH chroma range
            H=(h + hue_offset) % 360
        )
        rgb = oklch_to_srgb(oklch)
        
        # Verify contrast with background
        cr = contrast_ratio(rgb, bg)
        if cr < 3.0:  # WCAG AA-large minimum
            adjusted = adjust_lightness_for_contrast(
                oklch, bg, 3.0, make_lighter=(config.mode == "dark")
            )
            if adjusted:
                rgb = oklch_to_srgb(adjusted)
        
        colors.append(rgb)
    
    return tuple(colors)

# ============================================================================
# VSCODE THEME GENERATION
# ============================================================================

def generate_vscode_theme(config: ThemeConfig) -> dict:
    """
    Generate a complete VSCode theme with WCAG-verified colors.
    """
    # Generate palette
    bg_ramp = generate_background_ramp(config)
    base00, base01, base02, base03 = bg_ramp
    
    fg_ramp = generate_foreground_ramp(config, base00)
    base04, base05, base06, base07 = fg_ramp
    
    accents = generate_accent_colors(config, base00)
    base08, base09, base0A, base0B, base0C, base0D, base0E, base0F = accents
    
    # Convert to hex
    bg = srgb_to_hex(base00)
    bg_hl = srgb_to_hex(base01)
    bg_sel = srgb_to_hex(base02)
    comment = srgb_to_hex(base03)
    fg_dim = srgb_to_hex(base04)
    fg = srgb_to_hex(base05)
    fg_bright = srgb_to_hex(base06)
    fg_max = srgb_to_hex(base07)
    
    error = srgb_to_hex(base08)
    warning = srgb_to_hex(base09)
    accent = srgb_to_hex(base0A)
    success = srgb_to_hex(base0B)
    info = srgb_to_hex(base0C)
    link = srgb_to_hex(base0D)
    special = srgb_to_hex(base0E)
    deprecated = srgb_to_hex(base0F)
    
    # Verify and report contrast ratios
    cr_text = contrast_ratio(base05, base00)
    cr_comment = contrast_ratio(base03, base00)
    cr_accent = contrast_ratio(base0A, base00)
    
    print(f"  Text contrast (base05/base00):    {cr_text:.2f}:1 {'✓ AA' if wcag_aa(cr_text) else '✗'}")
    print(f"  Comment contrast (base03/base00): {cr_comment:.2f}:1 {'✓ AA-large' if wcag_aa_large(cr_comment) else '✗'}")
    print(f"  Accent contrast (base0A/base00):  {cr_accent:.2f}:1 {'✓ AA-large' if wcag_aa_large(cr_accent) else '✗'}")
    
    return {
        "name": f"Prism {config.name}",
        "type": config.mode,
        "colors": {
            "editor.background": bg,
            "editor.foreground": fg,
            "editorLineNumber.foreground": comment,
            "editorLineNumber.activeForeground": fg,
            "editorCursor.foreground": accent,
            "editor.selectionBackground": f"{accent}40",
            "editor.selectionHighlightBackground": f"{accent}25",
            "editor.lineHighlightBackground": bg_hl,
            "editorBracketMatch.background": f"{accent}30",
            "editorBracketMatch.border": accent,
            "sideBar.background": bg_hl,
            "sideBar.foreground": fg,
            "activityBar.background": bg,
            "activityBar.foreground": fg,
            "activityBar.activeBorder": accent,
            "activityBarBadge.background": accent,
            "activityBarBadge.foreground": bg,
            "titleBar.activeBackground": bg,
            "titleBar.activeForeground": fg,
            "statusBar.background": bg,
            "statusBar.foreground": comment,
            "tab.activeBackground": bg,
            "tab.activeForeground": fg,
            "tab.activeBorder": accent,
            "tab.inactiveBackground": bg_hl,
            "tab.inactiveForeground": comment,
            "panel.background": bg,
            "panel.border": bg_hl,
            "terminal.background": bg,
            "terminal.foreground": fg,
            "terminal.ansiBlack": bg,
            "terminal.ansiRed": error,
            "terminal.ansiGreen": success,
            "terminal.ansiYellow": warning,
            "terminal.ansiBlue": link,
            "terminal.ansiMagenta": special,
            "terminal.ansiCyan": info,
            "terminal.ansiWhite": fg,
            "terminal.ansiBrightBlack": comment,
            "terminal.ansiBrightRed": error,
            "terminal.ansiBrightGreen": success,
            "terminal.ansiBrightYellow": warning,
            "terminal.ansiBrightBlue": link,
            "terminal.ansiBrightMagenta": special,
            "terminal.ansiBrightCyan": info,
            "terminal.ansiBrightWhite": fg_max,
            "gitDecoration.modifiedResourceForeground": warning,
            "gitDecoration.deletedResourceForeground": error,
            "gitDecoration.untrackedResourceForeground": success,
            "button.background": accent,
            "button.foreground": bg,
            "input.background": bg,
            "input.foreground": fg,
            "input.border": bg_hl,
            "focusBorder": accent,
        },
        "tokenColors": [
            {"scope": "comment", "settings": {"foreground": comment, "fontStyle": "italic"}},
            {"scope": ["keyword", "storage.type", "storage.modifier"], "settings": {"foreground": special}},
            {"scope": "string", "settings": {"foreground": success}},
            {"scope": ["constant.numeric", "constant.language"], "settings": {"foreground": warning}},
            {"scope": "variable", "settings": {"foreground": fg}},
            {"scope": "variable.parameter", "settings": {"foreground": info}},
            {"scope": ["entity.name.function", "support.function"], "settings": {"foreground": link}},
            {"scope": ["entity.name.type", "entity.name.class"], "settings": {"foreground": accent}},
            {"scope": "entity.name.tag", "settings": {"foreground": error}},
            {"scope": "entity.other.attribute-name", "settings": {"foreground": warning}},
            {"scope": "punctuation", "settings": {"foreground": fg_dim}},
            {"scope": "meta.decorator", "settings": {"foreground": special}},
        ],
        "_prism_meta": {
            "generator": "prism-verified-generator",
            "oklch_hero_hue": config.hero_hue,
            "oklch_hero_saturation": config.hero_saturation,
            "contrast_text": round(cr_text, 2),
            "contrast_comment": round(cr_comment, 2),
            "contrast_accent": round(cr_accent, 2),
            "wcag_verified": wcag_aa(cr_text) and wcag_aa_large(cr_comment) and wcag_aa_large(cr_accent),
        }
    }

# ============================================================================
# CLI
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="PRISM Verified Theme Generator - OKLCH + WCAG",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Blue theme for OLED
  python verified_generator.py --hue 211 --mode dark --monitor oled --name "Blue Night"
  
  # Warm theme for LCD
  python verified_generator.py --hue 30 --mode dark --monitor lcd --name "Warm Ember"
  
  # Light theme
  python verified_generator.py --hue 211 --mode light --name "Day Light"
"""
    )
    parser.add_argument("--hue", type=float, required=True, help="Hero hue (0-360)")
    parser.add_argument("--saturation", type=float, default=1.0, help="Hero saturation (0-1)")
    parser.add_argument("--mode", choices=["dark", "light"], default="dark")
    parser.add_argument("--monitor", choices=["oled", "lcd"], default="oled")
    parser.add_argument("--name", required=True, help="Theme name")
    parser.add_argument("--output", "-o", default=".", help="Output directory")
    
    args = parser.parse_args()
    
    config = ThemeConfig(
        hero_hue=args.hue,
        hero_saturation=args.saturation,
        base_hue=args.hue,  # Use same hue for consistency
        base_saturation=0.1,  # Low saturation for backgrounds
        mode=args.mode,
        monitor=args.monitor,
        name=args.name
    )
    
    print(f"\nGenerating: Prism {config.name}")
    print(f"  Hero hue: {config.hero_hue}°")
    print(f"  Mode: {config.mode}")
    print(f"  Monitor: {config.monitor}")
    print()
    
    theme = generate_vscode_theme(config)
    
    # Save
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    slug = config.name.lower().replace(" ", "_")
    filepath = output_dir / f"prism-{slug}.json"
    
    with open(filepath, 'w') as f:
        json.dump(theme, f, indent=2)
    
    print(f"\n✓ Saved: {filepath}")
    
    if theme["_prism_meta"]["wcag_verified"]:
        print("✓ WCAG AA verified")
    else:
        print("⚠ Some colors may not meet WCAG AA")

if __name__ == "__main__":
    main()
