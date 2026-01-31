#!/usr/bin/env python3
"""
Prism Color Tools - Terminal Contrast Checker

A TUI for verifying WCAG compliance and exploring OKLCH color space.
Part of the Prism Theme System.

Usage:
    python contrast_checker.py
    python contrast_checker.py --theme fleek.json
"""

import sys
import math
from typing import Tuple, Optional

# OKLCH and sRGB conversion functions
# These mirror the formally verified Lean4 implementations

def srgb_to_linear(c: float) -> float:
    """sRGB gamma expansion (verified in Lean4: srgbToLinearComponent)"""
    if c <= 0.04045:
        return c / 12.92
    return ((c + 0.055) / 1.055) ** 2.4

def linear_to_srgb(c: float) -> float:
    """sRGB gamma compression (verified in Lean4: linearToSrgbComponent)"""
    if c <= 0.0031308:
        return 12.92 * c
    return 1.055 * (c ** (1/2.4)) - 0.055

def relative_luminance(r: float, g: float, b: float) -> float:
    """WCAG relative luminance (verified in Lean4: relativeLuminance)"""
    r_lin = srgb_to_linear(r)
    g_lin = srgb_to_linear(g)
    b_lin = srgb_to_linear(b)
    return 0.2126 * r_lin + 0.7152 * g_lin + 0.0722 * b_lin

def contrast_ratio(l1: float, l2: float) -> float:
    """WCAG contrast ratio (verified in Lean4: contrastRatio)
    
    Theorem: contrastRatio_ge_one proves this is always ≥ 1
    """
    lighter = max(l1, l2)
    darker = min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)

def hex_to_rgb(hex_color: str) -> Tuple[float, float, float]:
    """Parse hex color to RGB floats in [0,1]"""
    hex_color = hex_color.lstrip('#')
    r = int(hex_color[0:2], 16) / 255
    g = int(hex_color[2:4], 16) / 255
    b = int(hex_color[4:6], 16) / 255
    return (r, g, b)

def rgb_to_hex(r: float, g: float, b: float) -> str:
    """RGB floats to hex string"""
    return f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"

def oklch_to_oklab(l: float, c: float, h: float) -> Tuple[float, float, float]:
    """OKLCH to OKLAB (verified in Lean4: oklchToOklab)"""
    h_rad = h * (math.pi / 180)
    a = c * math.cos(h_rad)
    b = c * math.sin(h_rad)
    return (l, a, b)

def oklab_to_xyz(l: float, a: float, b: float) -> Tuple[float, float, float]:
    """OKLAB to XYZ (verified in Lean4: oklabToXYZ)"""
    l_ = l + 0.3963377774 * a + 0.2158037573 * b
    m_ = l - 0.1055613458 * a - 0.0638541728 * b
    s_ = l - 0.0894841775 * a - 1.2914855480 * b
    
    lms_l = l_ ** 3
    lms_m = m_ ** 3
    lms_s = s_ ** 3
    
    x = 1.2270138511 * lms_l - 0.5577999807 * lms_m + 0.2812561490 * lms_s
    y = -0.0405801784 * lms_l + 1.1122568696 * lms_m - 0.0716766787 * lms_s
    z = -0.0763812845 * lms_l - 0.4214819784 * lms_m + 1.5861632204 * lms_s
    
    return (max(0, x), max(0, y), max(0, z))

def xyz_to_linear_rgb(x: float, y: float, z: float) -> Tuple[float, float, float]:
    """XYZ to Linear RGB (verified in Lean4: xyzToLinear)"""
    r = max(0, min(1, 3.2404542 * x - 1.5371385 * y - 0.4985314 * z))
    g = max(0, min(1, -0.9692660 * x + 1.8760108 * y + 0.0415560 * z))
    b = max(0, min(1, 0.0556434 * x - 0.2040259 * y + 1.0572252 * z))
    return (r, g, b)

def oklch_to_srgb(l: float, c: float, h: float) -> Tuple[float, float, float]:
    """Full OKLCH to sRGB conversion chain"""
    ok_l, ok_a, ok_b = oklch_to_oklab(l, c, h)
    x, y, z = oklab_to_xyz(ok_l, ok_a, ok_b)
    r_lin, g_lin, b_lin = xyz_to_linear_rgb(x, y, z)
    return (linear_to_srgb(r_lin), linear_to_srgb(g_lin), linear_to_srgb(b_lin))

def wcag_rating(ratio: float) -> str:
    """Get WCAG compliance level"""
    if ratio >= 7.0:
        return "AAA ✓✓✓"
    elif ratio >= 4.5:
        return "AA ✓✓"
    elif ratio >= 3.0:
        return "AA-Large ✓"
    else:
        return "FAIL ✗"

def print_color_block(hex_color: str, label: str = "") -> None:
    """Print a colored block using ANSI true color"""
    r, g, b = hex_to_rgb(hex_color)
    r_int, g_int, b_int = int(r*255), int(g*255), int(b*255)
    # True color ANSI escape: \x1b[48;2;R;G;Bm for background
    block = f"\x1b[48;2;{r_int};{g_int};{b_int}m    \x1b[0m"
    lum = relative_luminance(r, g, b)
    print(f"{block} {hex_color} L={lum:.3f} {label}")

def check_contrast(fg: str, bg: str) -> None:
    """Check contrast between two colors"""
    fg_rgb = hex_to_rgb(fg)
    bg_rgb = hex_to_rgb(bg)
    
    fg_lum = relative_luminance(*fg_rgb)
    bg_lum = relative_luminance(*bg_rgb)
    
    ratio = contrast_ratio(fg_lum, bg_lum)
    rating = wcag_rating(ratio)
    
    print(f"\n{'═' * 50}")
    print("CONTRAST CHECK")
    print(f"{'═' * 50}")
    print_color_block(bg, "Background")
    print_color_block(fg, "Foreground")
    print(f"\nContrast Ratio: {ratio:.2f}:1")
    print(f"WCAG Rating:   {rating}")
    print(f"{'═' * 50}\n")

def interactive_mode():
    """Interactive TUI for color exploration"""
    print("""
╔══════════════════════════════════════════════════════════════╗
║                    PRISM COLOR TOOLS                        ║
║            Formally Verified Color Science                   ║
╚══════════════════════════════════════════════════════════════╝

Commands:
  contrast <fg> <bg>   - Check contrast ratio between two hex colors
  oklch <L> <C> <H>    - Convert OKLCH to hex (L:0-1, C:0-0.4, H:0-360)
  luminance <hex>      - Calculate relative luminance
  quit                 - Exit

Examples:
  contrast #f0ece0 #0a0a0a
  oklch 0.7 0.15 145
  luminance #3cb878
""")
    
    while True:
        try:
            line = input("prism> ").strip()
            if not line:
                continue
                
            parts = line.split()
            cmd = parts[0].lower()
            
            if cmd in ('quit', 'exit', 'q'):
                print("\n✨ Keep making beautiful things.\n")
                break
            elif cmd == 'contrast' and len(parts) == 3:
                check_contrast(parts[1], parts[2])
            elif cmd == 'oklch' and len(parts) == 4:
                l, c, h = float(parts[1]), float(parts[2]), float(parts[3])
                r, g, b = oklch_to_srgb(l, c, h)
                hex_color = rgb_to_hex(r, g, b)
                print(f"\nOKLCH({l}, {c}, {h}°) → {hex_color}")
                print_color_block(hex_color)
                print()
            elif cmd == 'luminance' and len(parts) == 2:
                r, g, b = hex_to_rgb(parts[1])
                lum = relative_luminance(r, g, b)
                print(f"\nRelative Luminance: {lum:.4f}")
                print_color_block(parts[1])
                print()
            else:
                print("Unknown command. Type 'quit' to exit.")
        except KeyboardInterrupt:
            print("\n")
            break
        except Exception as e:
            print(f"Error: {e}")

if __name__ == "__main__":
    if len(sys.argv) == 1:
        interactive_mode()
    elif sys.argv[1] == '--help':
        print(__doc__)
    else:
        print("Usage: python contrast_checker.py")
        print("       python contrast_checker.py --help")
