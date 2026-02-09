#!/usr/bin/env python3
"""
Prism Theme Validator

Validates all themes for WCAG compliance and color science correctness.
Used for CI/CD and quality assurance.

Usage:
    python validate_themes.py themes/
    python validate_themes.py fleek.json
"""

import json
import sys
import os
from pathlib import Path
from typing import Dict, List, Tuple, Any

# Import from contrast_checker
from contrast_checker import (
    hex_to_rgb, relative_luminance, contrast_ratio, wcag_rating
)

class ValidationError:
    def __init__(self, theme: str, check: str, message: str, severity: str = "error"):
        self.theme = theme
        self.check = check
        self.message = message
        self.severity = severity  # "error", "warning", "info"
    
    def __str__(self):
        icon = {"error": "✗", "warning": "⚠", "info": "ℹ"}[self.severity]
        return f"  {icon} [{self.check}] {self.message}"

def validate_hex_color(color: str) -> bool:
    """Check if a string is a valid hex color"""
    if not color.startswith('#'):
        return False
    try:
        int(color[1:], 16)
        return len(color) in (4, 7)  # #RGB or #RRGGBB
    except:
        return False

def validate_contrast(fg: str, bg: str, min_ratio: float, label: str) -> Tuple[float, bool]:
    """Check contrast ratio between two colors"""
    fg_rgb = hex_to_rgb(fg)
    bg_rgb = hex_to_rgb(bg)
    fg_lum = relative_luminance(*fg_rgb)
    bg_lum = relative_luminance(*bg_rgb)
    ratio = contrast_ratio(fg_lum, bg_lum)
    return ratio, ratio >= min_ratio

def validate_lightness(color: str, min_l: float, max_l: float) -> Tuple[float, bool]:
    """Check if color lightness is in range"""
    r, g, b = hex_to_rgb(color)
    lum = relative_luminance(r, g, b)
    return lum, min_l <= lum <= max_l

def validate_theme(theme_path: Path) -> List[ValidationError]:
    """Validate a single theme file"""
    errors = []
    theme_name = theme_path.stem
    
    try:
        with open(theme_path) as f:
            theme = json.load(f)
    except json.JSONDecodeError as e:
        errors.append(ValidationError(theme_name, "parse", f"Invalid JSON: {e}", "error"))
        return errors
    except Exception as e:
        errors.append(ValidationError(theme_name, "read", f"Could not read file: {e}", "error"))
        return errors
    
    # Get colors
    colors = theme.get("colors", {})
    if not colors:
        errors.append(ValidationError(theme_name, "structure", "Missing 'colors' object", "error"))
        return errors
    
    # Required colors
    bg = colors.get("background")
    fg = colors.get("text")
    muted = colors.get("textMuted")
    accent = colors.get("accent")
    
    if not bg:
        errors.append(ValidationError(theme_name, "required", "Missing 'background' color", "error"))
    if not fg:
        errors.append(ValidationError(theme_name, "required", "Missing 'text' color", "error"))
    
    if not bg or not fg:
        return errors
    
    # Validate hex format
    for key, value in colors.items():
        if isinstance(value, str) and value.startswith('#'):
            if not validate_hex_color(value):
                errors.append(ValidationError(theme_name, "format", f"Invalid hex: {key}={value}", "error"))
    
    # WCAG Contrast Checks
    # Normal text: 4.5:1
    ratio, passes = validate_contrast(fg, bg, 4.5, "text/bg")
    if not passes:
        errors.append(ValidationError(
            theme_name, "wcag-aa", 
            f"Text contrast {ratio:.2f}:1 < 4.5:1 ({fg} on {bg})", 
            "error"
        ))
    
    # Muted text: 3.0:1 (large text threshold)
    if muted:
        ratio, passes = validate_contrast(muted, bg, 3.0, "muted/bg")
        if not passes:
            errors.append(ValidationError(
                theme_name, "wcag-aa-large",
                f"Muted text contrast {ratio:.2f}:1 < 3.0:1 ({muted} on {bg})",
                "warning"
            ))
    
    # Accent visibility
    if accent:
        ratio, passes = validate_contrast(accent, bg, 3.0, "accent/bg")
        if not passes:
            errors.append(ValidationError(
                theme_name, "accent",
                f"Accent contrast {ratio:.2f}:1 < 3.0:1 ({accent} on {bg})",
                "warning"
            ))
    
    # Syntax colors
    syntax = colors.get("syntax", {})
    for key, color in syntax.items():
        if isinstance(color, str) and color.startswith('#'):
            ratio, passes = validate_contrast(color, bg, 3.0, f"syntax.{key}")
            if not passes:
                errors.append(ValidationError(
                    theme_name, "syntax",
                    f"syntax.{key} contrast {ratio:.2f}:1 < 3.0:1 ({color} on {bg})",
                    "warning"
                ))
    
    # Dark theme black balance check
    theme_type = theme.get("type", "dark")
    if theme_type == "dark":
        r, g, b = hex_to_rgb(bg)
        lum = relative_luminance(r, g, b)
        if lum < 0.005:  # True black
            errors.append(ValidationError(
                theme_name, "oled",
                f"Background too dark (L={lum:.4f}) - may cause OLED smearing",
                "info"
            ))
    
    return errors

def validate_directory(dir_path: Path) -> Dict[str, List[ValidationError]]:
    """Validate all themes in a directory"""
    results = {}
    
    for theme_file in sorted(dir_path.glob("*.json")):
        errors = validate_theme(theme_file)
        if errors:
            results[theme_file.name] = errors
    
    return results

def main():
    if len(sys.argv) < 2:
        print("Usage: python validate_themes.py <path>")
        print("       path can be a .json file or directory")
        sys.exit(1)
    
    path = Path(sys.argv[1])
    
    print("""
╔══════════════════════════════════════════════════════════════╗
║                  PRISM THEME VALIDATOR                       ║
║            WCAG Compliance & Color Science                   ║
╚══════════════════════════════════════════════════════════════╝
""")
    
    if path.is_file():
        errors = validate_theme(path)
        results = {path.name: errors} if errors else {}
        total_themes = 1
    elif path.is_dir():
        results = validate_directory(path)
        total_themes = len(list(path.glob("*.json")))
    else:
        print(f"Error: {path} not found")
        sys.exit(1)
    
    # Print results
    error_count = 0
    warning_count = 0
    
    for theme_name, errors in results.items():
        print(f"\n{theme_name}:")
        for error in errors:
            print(error)
            if error.severity == "error":
                error_count += 1
            elif error.severity == "warning":
                warning_count += 1
    
    # Summary
    passed = total_themes - len(results)
    print(f"\n{'═' * 60}")
    print(f"Validated: {total_themes} themes")
    print(f"Passed:    {passed} ✓")
    print(f"Issues:    {len(results)} themes with issues")
    print(f"  Errors:   {error_count}")
    print(f"  Warnings: {warning_count}")
    print(f"{'═' * 60}\n")
    
    # Exit code
    sys.exit(1 if error_count > 0 else 0)

if __name__ == "__main__":
    main()
