#!/usr/bin/env python3
"""
Generate terminal emulator themes from Prism source themes.

Supports: Alacritty, Kitty, WezTerm, iTerm2

Usage:
    python generate_terminal_themes.py
"""

import json
import os
import plistlib
from pathlib import Path
from typing import Dict

# Base path
SCRIPT_DIR = Path(__file__).parent
THEMES_DIR = SCRIPT_DIR.parent.parent / "prism-code" / "themes"
OUTPUT_DIR = SCRIPT_DIR.parent.parent / "terminal-themes"

def hex_to_rgb_int(hex_color: str) -> tuple:
    """Convert hex to RGB integers (0-255)"""
    h = hex_color.lstrip('#')
    return tuple(int(h[i:i+2], 16) for i in (0, 2, 4))

def hex_to_rgb_float(hex_color: str) -> tuple:
    """Convert hex to RGB floats (0-1)"""
    r, g, b = hex_to_rgb_int(hex_color)
    return (r/255, g/255, b/255)

def get_terminal_colors(theme: dict) -> dict:
    """Extract ANSI colors from theme"""
    colors = theme.get("colors", {})
    terminal = colors.get("terminal", theme.get("terminal", {}).get("ansi", {}))
    
    is_dark = theme.get("type", "dark") == "dark"
    
    bg = colors.get("background", "#1a1a1a")
    fg = colors.get("text", "#e0e0e0")
    syntax = colors.get("syntax", {})
    
    # Build ANSI colors from syntax colors where available
    ansi = {
        "black": terminal.get("black", "#0a0a0a" if is_dark else "#1a1a1a"),
        "red": terminal.get("red", syntax.get("error", syntax.get("keyword", "#ff5555"))),
        "green": terminal.get("green", syntax.get("string", "#50fa7b")),
        "yellow": terminal.get("yellow", syntax.get("number", syntax.get("warning", "#f1fa8c"))),
        "blue": terminal.get("blue", colors.get("accent", "#6272a4")),
        "magenta": terminal.get("magenta", syntax.get("keyword", "#ff79c6")),
        "cyan": terminal.get("cyan", syntax.get("type", "#8be9fd")),
        "white": terminal.get("white", fg if is_dark else "#44475a"),
        "brightBlack": terminal.get("brightBlack", colors.get("textMuted", "#6272a4")),
        "brightRed": terminal.get("brightRed", "#ff6e6e"),
        "brightGreen": terminal.get("brightGreen", "#69ff94"),
        "brightYellow": terminal.get("brightYellow", "#ffffa5"),
        "brightBlue": terminal.get("brightBlue", "#d6acff"),
        "brightMagenta": terminal.get("brightMagenta", "#ff92df"),
        "brightCyan": terminal.get("brightCyan", "#a4ffff"),
        "brightWhite": terminal.get("brightWhite", "#ffffff"),
    }
    
    return {
        "bg": bg,
        "fg": fg,
        "cursor": colors.get("cursor", colors.get("accent", fg)),
        "selection_bg": colors.get("selection", {}).get("background") if isinstance(colors.get("selection"), dict) else "#44475a",
        "selection_fg": colors.get("selection", {}).get("text") if isinstance(colors.get("selection"), dict) else fg,
        **ansi
    }


def generate_alacritty(name: str, colors: dict) -> str:
    return f'''# Prism Theme: {name}
# https://github.com/weylai/prism-themes

[colors.primary]
background = "{colors['bg']}"
foreground = "{colors['fg']}"

[colors.cursor]
text = "{colors['bg']}"
cursor = "{colors['cursor']}"

[colors.selection]
text = "{colors['selection_fg']}"
background = "{colors['selection_bg']}"

[colors.normal]
black = "{colors['black']}"
red = "{colors['red']}"
green = "{colors['green']}"
yellow = "{colors['yellow']}"
blue = "{colors['blue']}"
magenta = "{colors['magenta']}"
cyan = "{colors['cyan']}"
white = "{colors['white']}"

[colors.bright]
black = "{colors['brightBlack']}"
red = "{colors['brightRed']}"
green = "{colors['brightGreen']}"
yellow = "{colors['brightYellow']}"
blue = "{colors['brightBlue']}"
magenta = "{colors['brightMagenta']}"
cyan = "{colors['brightCyan']}"
white = "{colors['brightWhite']}"
'''


def generate_kitty(name: str, colors: dict) -> str:
    return f'''# Prism Theme: {name}
# https://github.com/weylai/prism-themes

foreground {colors['fg']}
background {colors['bg']}

cursor {colors['cursor']}
cursor_text_color {colors['bg']}

selection_foreground {colors['selection_fg']}
selection_background {colors['selection_bg']}

# black
color0 {colors['black']}
color8 {colors['brightBlack']}

# red
color1 {colors['red']}
color9 {colors['brightRed']}

# green
color2 {colors['green']}
color10 {colors['brightGreen']}

# yellow
color3 {colors['yellow']}
color11 {colors['brightYellow']}

# blue
color4 {colors['blue']}
color12 {colors['brightBlue']}

# magenta
color5 {colors['magenta']}
color13 {colors['brightMagenta']}

# cyan
color6 {colors['cyan']}
color14 {colors['brightCyan']}

# white
color7 {colors['white']}
color15 {colors['brightWhite']}
'''


def generate_wezterm(name: str, colors: dict) -> str:
    return f'''# Prism Theme: {name}
# https://github.com/weylai/prism-themes

[colors]
foreground = "{colors['fg']}"
background = "{colors['bg']}"

cursor_bg = "{colors['cursor']}"
cursor_fg = "{colors['bg']}"
cursor_border = "{colors['cursor']}"

selection_fg = "{colors['selection_fg']}"
selection_bg = "{colors['selection_bg']}"

ansi = [
    "{colors['black']}",
    "{colors['red']}",
    "{colors['green']}",
    "{colors['yellow']}",
    "{colors['blue']}",
    "{colors['magenta']}",
    "{colors['cyan']}",
    "{colors['white']}"
]

brights = [
    "{colors['brightBlack']}",
    "{colors['brightRed']}",
    "{colors['brightGreen']}",
    "{colors['brightYellow']}",
    "{colors['brightBlue']}",
    "{colors['brightMagenta']}",
    "{colors['brightCyan']}",
    "{colors['brightWhite']}"
]

[metadata]
name = "Prism {name}"
author = "Prism Themes"
'''


def generate_iterm2(name: str, colors: dict) -> bytes:
    def color_dict(hex_color: str) -> dict:
        r, g, b = hex_to_rgb_float(hex_color)
        return {
            "Alpha Component": 1.0,
            "Blue Component": b,
            "Color Space": "sRGB",
            "Green Component": g,
            "Red Component": r,
        }
    
    plist = {
        "Ansi 0 Color": color_dict(colors['black']),
        "Ansi 1 Color": color_dict(colors['red']),
        "Ansi 2 Color": color_dict(colors['green']),
        "Ansi 3 Color": color_dict(colors['yellow']),
        "Ansi 4 Color": color_dict(colors['blue']),
        "Ansi 5 Color": color_dict(colors['magenta']),
        "Ansi 6 Color": color_dict(colors['cyan']),
        "Ansi 7 Color": color_dict(colors['white']),
        "Ansi 8 Color": color_dict(colors['brightBlack']),
        "Ansi 9 Color": color_dict(colors['brightRed']),
        "Ansi 10 Color": color_dict(colors['brightGreen']),
        "Ansi 11 Color": color_dict(colors['brightYellow']),
        "Ansi 12 Color": color_dict(colors['brightBlue']),
        "Ansi 13 Color": color_dict(colors['brightMagenta']),
        "Ansi 14 Color": color_dict(colors['brightCyan']),
        "Ansi 15 Color": color_dict(colors['brightWhite']),
        "Background Color": color_dict(colors['bg']),
        "Bold Color": color_dict(colors['fg']),
        "Cursor Color": color_dict(colors['cursor']),
        "Cursor Text Color": color_dict(colors['bg']),
        "Foreground Color": color_dict(colors['fg']),
        "Selected Text Color": color_dict(colors['selection_fg']),
        "Selection Color": color_dict(colors['selection_bg']),
    }
    
    return plistlib.dumps(plist)


def main():
    print("Prism Terminal Theme Generator")
    print("=" * 50)
    
    if not THEMES_DIR.exists():
        print(f"Error: Themes directory not found: {THEMES_DIR}")
        return 1
    
    for subdir in ["alacritty", "kitty", "wezterm", "iterm2"]:
        (OUTPUT_DIR / subdir).mkdir(parents=True, exist_ok=True)
    
    theme_count = 0
    
    for theme_file in sorted(THEMES_DIR.glob("*.json")):
        try:
            with open(theme_file) as f:
                theme = json.load(f)
            
            name = theme_file.stem
            colors = get_terminal_colors(theme)
            theme_count += 1
            
            (OUTPUT_DIR / "alacritty" / f"{name}.toml").write_text(generate_alacritty(name, colors))
            (OUTPUT_DIR / "kitty" / f"{name}.conf").write_text(generate_kitty(name, colors))
            (OUTPUT_DIR / "wezterm" / f"{name}.toml").write_text(generate_wezterm(name, colors))
            (OUTPUT_DIR / "iterm2" / f"{name}.itermcolors").write_bytes(generate_iterm2(name, colors))
            
            print(f"  ✓ {name}")
            
        except Exception as e:
            print(f"  ✗ {theme_file.name}: {e}")
    
    print("=" * 50)
    print(f"Generated {theme_count} themes for 4 terminal emulators")
    print(f"Output: {OUTPUT_DIR}")
    
    return 0

if __name__ == "__main__":
    exit(main())
