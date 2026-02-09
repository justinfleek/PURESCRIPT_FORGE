#!/usr/bin/env python3
"""
Generate themes for ALL supported platforms from Prism source themes.

Supports:
- Terminal Emulators: Alacritty, Kitty, WezTerm, iTerm2, Windows Terminal
- Editors: VS Code, JetBrains, Zed, Helix
- CLI Tools: bat, delta, starship, tmux

Usage:
    python generate_all_themes.py
"""

import json
import plistlib
from pathlib import Path
from typing import Dict, Tuple

# ═══════════════════════════════════════════════════════════════════
# Configuration
# ═══════════════════════════════════════════════════════════════════

SCRIPT_DIR = Path(__file__).parent
THEMES_DIR = SCRIPT_DIR.parent.parent / "prism-code" / "themes"
OUTPUT_BASE = SCRIPT_DIR.parent.parent / "terminal-themes"

# ═══════════════════════════════════════════════════════════════════
# Color Utilities
# ═══════════════════════════════════════════════════════════════════

def hex_to_rgb_int(hex_color: str) -> Tuple[int, int, int]:
    h = hex_color.lstrip('#')
    return tuple(int(h[i:i+2], 16) for i in (0, 2, 4))

def hex_to_rgb_float(hex_color: str) -> Tuple[float, float, float]:
    r, g, b = hex_to_rgb_int(hex_color)
    return (r/255, g/255, b/255)

def lighten_hex(hex_color: str, amount: float = 0.2) -> str:
    r, g, b = hex_to_rgb_int(hex_color)
    r = min(255, int(r + (255 - r) * amount))
    g = min(255, int(g + (255 - g) * amount))
    b = min(255, int(b + (255 - b) * amount))
    return f"#{r:02x}{g:02x}{b:02x}"

def get_terminal_colors(theme: dict) -> dict:
    """Extract comprehensive colors from theme"""
    colors = theme.get("colors", {})
    terminal = colors.get("terminal", {})
    syntax = colors.get("syntax", {})
    
    is_dark = theme.get("type", "dark") == "dark"
    
    bg = colors.get("background", "#1a1a1a")
    fg = colors.get("text", "#e0e0e0")
    accent = colors.get("accent", "#00a0e4")
    muted = colors.get("textMuted", "#808080")
    
    return {
        "bg": bg,
        "fg": fg,
        "cursor": colors.get("cursor", accent),
        "selection_bg": colors.get("selection", {}).get("background", "#44475a") if isinstance(colors.get("selection"), dict) else "#44475a",
        "selection_fg": fg,
        "muted": muted,
        "accent": accent,
        
        # Syntax
        "keyword": syntax.get("keyword", "#ff79c6"),
        "string": syntax.get("string", "#f1fa8c"),
        "function": syntax.get("function", "#50fa7b"),
        "comment": syntax.get("comment", "#6272a4"),
        "number": syntax.get("number", "#bd93f9"),
        "type": syntax.get("type", "#8be9fd"),
        
        # ANSI Normal
        "black": terminal.get("black", "#0a0a0a" if is_dark else "#1a1a1a"),
        "red": terminal.get("red", syntax.get("keyword", "#ff5555")),
        "green": terminal.get("green", syntax.get("string", "#50fa7b")),
        "yellow": terminal.get("yellow", syntax.get("number", "#f1fa8c")),
        "blue": terminal.get("blue", accent),
        "magenta": terminal.get("magenta", syntax.get("keyword", "#ff79c6")),
        "cyan": terminal.get("cyan", syntax.get("type", "#8be9fd")),
        "white": terminal.get("white", fg),
        
        # ANSI Bright
        "bright_black": terminal.get("brightBlack", muted),
        "bright_red": terminal.get("brightRed", lighten_hex(syntax.get("keyword", "#ff5555"))),
        "bright_green": terminal.get("brightGreen", lighten_hex(syntax.get("string", "#50fa7b"))),
        "bright_yellow": terminal.get("brightYellow", lighten_hex(syntax.get("number", "#f1fa8c"))),
        "bright_blue": terminal.get("brightBlue", lighten_hex(accent)),
        "bright_magenta": terminal.get("brightMagenta", lighten_hex(syntax.get("keyword", "#ff79c6"))),
        "bright_cyan": terminal.get("brightCyan", lighten_hex(syntax.get("type", "#8be9fd"))),
        "bright_white": terminal.get("brightWhite", "#ffffff"),
    }

# ═══════════════════════════════════════════════════════════════════
# Generators
# ═══════════════════════════════════════════════════════════════════

def gen_alacritty(name: str, c: dict) -> str:
    return f'''# Prism Theme: {name}
# https://github.com/weylai/prism-themes

[colors.primary]
background = "{c['bg']}"
foreground = "{c['fg']}"

[colors.cursor]
text = "{c['bg']}"
cursor = "{c['cursor']}"

[colors.selection]
text = "{c['selection_fg']}"
background = "{c['selection_bg']}"

[colors.normal]
black = "{c['black']}"
red = "{c['red']}"
green = "{c['green']}"
yellow = "{c['yellow']}"
blue = "{c['blue']}"
magenta = "{c['magenta']}"
cyan = "{c['cyan']}"
white = "{c['white']}"

[colors.bright]
black = "{c['bright_black']}"
red = "{c['bright_red']}"
green = "{c['bright_green']}"
yellow = "{c['bright_yellow']}"
blue = "{c['bright_blue']}"
magenta = "{c['bright_magenta']}"
cyan = "{c['bright_cyan']}"
white = "{c['bright_white']}"
'''

def gen_kitty(name: str, c: dict) -> str:
    return f'''# Prism Theme: {name}
foreground {c['fg']}
background {c['bg']}
cursor {c['cursor']}
cursor_text_color {c['bg']}
selection_foreground {c['selection_fg']}
selection_background {c['selection_bg']}

color0 {c['black']}
color8 {c['bright_black']}
color1 {c['red']}
color9 {c['bright_red']}
color2 {c['green']}
color10 {c['bright_green']}
color3 {c['yellow']}
color11 {c['bright_yellow']}
color4 {c['blue']}
color12 {c['bright_blue']}
color5 {c['magenta']}
color13 {c['bright_magenta']}
color6 {c['cyan']}
color14 {c['bright_cyan']}
color7 {c['white']}
color15 {c['bright_white']}
'''

def gen_wezterm(name: str, c: dict) -> str:
    return f'''# Prism Theme: {name}
[colors]
foreground = "{c['fg']}"
background = "{c['bg']}"
cursor_bg = "{c['cursor']}"
cursor_fg = "{c['bg']}"
cursor_border = "{c['cursor']}"
selection_fg = "{c['selection_fg']}"
selection_bg = "{c['selection_bg']}"

ansi = ["{c['black']}", "{c['red']}", "{c['green']}", "{c['yellow']}", "{c['blue']}", "{c['magenta']}", "{c['cyan']}", "{c['white']}"]
brights = ["{c['bright_black']}", "{c['bright_red']}", "{c['bright_green']}", "{c['bright_yellow']}", "{c['bright_blue']}", "{c['bright_magenta']}", "{c['bright_cyan']}", "{c['bright_white']}"]

[metadata]
name = "Prism {name}"
'''

def gen_iterm2(name: str, c: dict) -> bytes:
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
        "Ansi 0 Color": color_dict(c['black']),
        "Ansi 1 Color": color_dict(c['red']),
        "Ansi 2 Color": color_dict(c['green']),
        "Ansi 3 Color": color_dict(c['yellow']),
        "Ansi 4 Color": color_dict(c['blue']),
        "Ansi 5 Color": color_dict(c['magenta']),
        "Ansi 6 Color": color_dict(c['cyan']),
        "Ansi 7 Color": color_dict(c['white']),
        "Ansi 8 Color": color_dict(c['bright_black']),
        "Ansi 9 Color": color_dict(c['bright_red']),
        "Ansi 10 Color": color_dict(c['bright_green']),
        "Ansi 11 Color": color_dict(c['bright_yellow']),
        "Ansi 12 Color": color_dict(c['bright_blue']),
        "Ansi 13 Color": color_dict(c['bright_magenta']),
        "Ansi 14 Color": color_dict(c['bright_cyan']),
        "Ansi 15 Color": color_dict(c['bright_white']),
        "Background Color": color_dict(c['bg']),
        "Bold Color": color_dict(c['fg']),
        "Cursor Color": color_dict(c['cursor']),
        "Cursor Text Color": color_dict(c['bg']),
        "Foreground Color": color_dict(c['fg']),
        "Selected Text Color": color_dict(c['selection_fg']),
        "Selection Color": color_dict(c['selection_bg']),
    }
    return plistlib.dumps(plist)

def gen_windows_terminal(name: str, c: dict) -> str:
    return json.dumps({
        "name": f"Prism {name}",
        "background": c['bg'],
        "foreground": c['fg'],
        "cursorColor": c['cursor'],
        "selectionBackground": c['selection_bg'],
        "black": c['black'],
        "red": c['red'],
        "green": c['green'],
        "yellow": c['yellow'],
        "blue": c['blue'],
        "purple": c['magenta'],
        "cyan": c['cyan'],
        "white": c['white'],
        "brightBlack": c['bright_black'],
        "brightRed": c['bright_red'],
        "brightGreen": c['bright_green'],
        "brightYellow": c['bright_yellow'],
        "brightBlue": c['bright_blue'],
        "brightPurple": c['bright_magenta'],
        "brightCyan": c['bright_cyan'],
        "brightWhite": c['bright_white']
    }, indent=2)

def gen_jetbrains(name: str, c: dict, theme_type: str) -> str:
    def to_jb(hex_color: str) -> str:
        return hex_color.lstrip('#').upper()
    
    parent = "Darcula" if theme_type == "dark" else "Default"
    
    return f'''<?xml version="1.0" encoding="UTF-8"?>
<scheme name="Prism {name}" version="142" parent_scheme="{parent}">
  <metaInfo>
    <property name="created">Prism Theme Generator</property>
    <property name="ideVersion">2024.1</property>
    <property name="modified">Prism Theme Generator</property>
  </metaInfo>
  <colors>
    <option name="CARET_COLOR" value="{to_jb(c['cursor'])}" />
    <option name="CARET_ROW_COLOR" value="{to_jb(lighten_hex(c['bg'], 0.05) if theme_type == 'dark' else lighten_hex(c['bg'], -0.05))}" />
    <option name="CONSOLE_BACKGROUND_KEY" value="{to_jb(c['bg'])}" />
    <option name="GUTTER_BACKGROUND" value="{to_jb(c['bg'])}" />
    <option name="LINE_NUMBERS_COLOR" value="{to_jb(c['muted'])}" />
    <option name="SELECTION_BACKGROUND" value="{to_jb(c['selection_bg'])}" />
    <option name="SELECTION_FOREGROUND" value="{to_jb(c['fg'])}" />
  </colors>
  <attributes>
    <option name="DEFAULT_KEYWORD">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['keyword'])}" />
        <option name="FONT_TYPE" value="1" />
      </value>
    </option>
    <option name="DEFAULT_STRING">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['string'])}" />
      </value>
    </option>
    <option name="DEFAULT_FUNCTION_DECLARATION">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['function'])}" />
      </value>
    </option>
    <option name="DEFAULT_FUNCTION_CALL">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['function'])}" />
      </value>
    </option>
    <option name="DEFAULT_LINE_COMMENT">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['comment'])}" />
        <option name="FONT_TYPE" value="2" />
      </value>
    </option>
    <option name="DEFAULT_BLOCK_COMMENT">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['comment'])}" />
        <option name="FONT_TYPE" value="2" />
      </value>
    </option>
    <option name="DEFAULT_DOC_COMMENT">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['comment'])}" />
        <option name="FONT_TYPE" value="2" />
      </value>
    </option>
    <option name="DEFAULT_NUMBER">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['number'])}" />
      </value>
    </option>
    <option name="DEFAULT_CLASS_NAME">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['type'])}" />
      </value>
    </option>
    <option name="DEFAULT_INTERFACE_NAME">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['type'])}" />
        <option name="FONT_TYPE" value="2" />
      </value>
    </option>
    <option name="DEFAULT_CONSTANT">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['number'])}" />
        <option name="FONT_TYPE" value="1" />
      </value>
    </option>
    <option name="DEFAULT_IDENTIFIER">
      <value>
        <option name="FOREGROUND" value="{to_jb(c['fg'])}" />
      </value>
    </option>
  </attributes>
</scheme>
'''

def gen_zed(name: str, c: dict, theme_type: str) -> str:
    return json.dumps({
        "$schema": "https://zed.dev/schema/themes/v0.1.0.json",
        "name": f"Prism {name}",
        "author": "Prism Theme System",
        "themes": [{
            "name": f"Prism {name}",
            "appearance": "dark" if theme_type == "dark" else "light",
            "style": {
                "background": c['bg'],
                "editor.background": c['bg'],
                "editor.foreground": c['fg'],
                "editor.gutter.background": c['bg'],
                "editor.line_highlight.background": lighten_hex(c['bg'], 0.03) if theme_type == "dark" else lighten_hex(c['bg'], -0.03),
                "editor.active_line_number": c['accent'],
                "editor.wrap_guide": c['muted'],
                "terminal.background": c['bg'],
                "terminal.foreground": c['fg'],
                "terminal.ansi.black": c['black'],
                "terminal.ansi.red": c['red'],
                "terminal.ansi.green": c['green'],
                "terminal.ansi.yellow": c['yellow'],
                "terminal.ansi.blue": c['blue'],
                "terminal.ansi.magenta": c['magenta'],
                "terminal.ansi.cyan": c['cyan'],
                "terminal.ansi.white": c['white'],
                "syntax": {
                    "comment": {"color": c['comment'], "font_style": "italic"},
                    "keyword": {"color": c['keyword'], "font_weight": 600},
                    "string": {"color": c['string']},
                    "function": {"color": c['function']},
                    "number": {"color": c['number']},
                    "type": {"color": c['type']},
                    "variable": {"color": c['fg']},
                    "constant": {"color": c['number']},
                    "attribute": {"color": c['type']},
                    "property": {"color": c['fg']},
                    "punctuation": {"color": c['fg']},
                    "operator": {"color": c['keyword']},
                }
            }
        }]
    }, indent=2)

def gen_helix(name: str, c: dict, theme_type: str) -> str:
    return f'''# Prism Theme: {name}
# Place in ~/.config/helix/themes/prism-{name}.toml

"ui.background" = {{ bg = "{c['bg']}" }}
"ui.text" = "{c['fg']}"
"ui.text.focus" = "{c['accent']}"
"ui.cursor" = {{ bg = "{c['cursor']}", fg = "{c['bg']}" }}
"ui.cursor.match" = {{ bg = "{c['selection_bg']}" }}
"ui.selection" = {{ bg = "{c['selection_bg']}" }}
"ui.linenr" = "{c['muted']}"
"ui.linenr.selected" = "{c['accent']}"
"ui.cursorline.primary" = {{ bg = "{lighten_hex(c['bg'], 0.03) if theme_type == 'dark' else lighten_hex(c['bg'], -0.03)}" }}
"ui.statusline" = {{ fg = "{c['fg']}", bg = "{c['bg']}" }}
"ui.statusline.inactive" = {{ fg = "{c['muted']}", bg = "{c['bg']}" }}
"ui.popup" = {{ bg = "{c['bg']}" }}
"ui.menu" = {{ bg = "{c['bg']}" }}
"ui.menu.selected" = {{ bg = "{c['selection_bg']}" }}
"ui.help" = {{ fg = "{c['fg']}", bg = "{c['bg']}" }}

"comment" = {{ fg = "{c['comment']}", modifiers = ["italic"] }}
"keyword" = {{ fg = "{c['keyword']}", modifiers = ["bold"] }}
"keyword.control" = "{c['keyword']}"
"keyword.function" = "{c['keyword']}"
"keyword.return" = "{c['keyword']}"
"keyword.exception" = "{c['keyword']}"
"keyword.operator" = "{c['keyword']}"

"string" = "{c['string']}"
"string.special" = "{c['string']}"

"function" = "{c['function']}"
"function.builtin" = "{c['function']}"
"function.method" = "{c['function']}"
"function.macro" = "{c['function']}"

"constant" = "{c['number']}"
"constant.numeric" = "{c['number']}"
"constant.character" = "{c['string']}"
"constant.builtin" = "{c['number']}"

"type" = "{c['type']}"
"type.builtin" = "{c['type']}"

"variable" = "{c['fg']}"
"variable.builtin" = "{c['type']}"
"variable.parameter" = "{c['fg']}"

"attribute" = "{c['type']}"
"namespace" = "{c['type']}"

"operator" = "{c['keyword']}"
"punctuation" = "{c['fg']}"
"punctuation.delimiter" = "{c['fg']}"
"punctuation.bracket" = "{c['fg']}"

"label" = "{c['accent']}"
"tag" = "{c['keyword']}"

"markup.heading" = {{ fg = "{c['keyword']}", modifiers = ["bold"] }}
"markup.bold" = {{ modifiers = ["bold"] }}
"markup.italic" = {{ modifiers = ["italic"] }}
"markup.link.url" = "{c['accent']}"
"markup.link.text" = "{c['string']}"
"markup.raw" = "{c['string']}"

"diff.plus" = "{c['green']}"
"diff.minus" = "{c['red']}"
"diff.delta" = "{c['yellow']}"

[palette]
background = "{c['bg']}"
foreground = "{c['fg']}"
accent = "{c['accent']}"
'''

def gen_bat(name: str, c: dict) -> str:
    """Generate bat/delta theme (TextMate/Sublime format)"""
    return json.dumps({
        "name": f"Prism {name}",
        "variables": {
            "bg": c['bg'],
            "fg": c['fg'],
        },
        "globals": {
            "background": c['bg'],
            "foreground": c['fg'],
            "caret": c['cursor'],
            "selection": c['selection_bg'],
            "line_highlight": lighten_hex(c['bg'], 0.03),
        },
        "rules": [
            {"scope": "comment", "foreground": c['comment'], "font_style": "italic"},
            {"scope": "keyword", "foreground": c['keyword']},
            {"scope": "string", "foreground": c['string']},
            {"scope": "entity.name.function", "foreground": c['function']},
            {"scope": "constant.numeric", "foreground": c['number']},
            {"scope": "entity.name.type, support.type", "foreground": c['type']},
            {"scope": "variable", "foreground": c['fg']},
        ]
    }, indent=2)

def gen_starship(name: str, c: dict) -> str:
    """Generate starship prompt theme snippet"""
    return f'''# Prism Theme: {name}
# Add to ~/.config/starship.toml

# Suggested color palette based on {name}
# You can reference these in your starship config

# Example usage:
# [character]
# success_symbol = "[❯](bold {c['green']})"
# error_symbol = "[❯](bold {c['red']})"

# [directory]
# style = "bold {c['accent']}"

# [git_branch]
# style = "bold {c['magenta']}"

# [git_status]
# style = "{c['yellow']}"

# Color reference:
# background: {c['bg']}
# foreground: {c['fg']}
# accent: {c['accent']}
# keyword: {c['keyword']}
# string: {c['string']}
# function: {c['function']}
# comment: {c['comment']}
# number: {c['number']}
# type: {c['type']}
'''

def gen_tmux(name: str, c: dict) -> str:
    """Generate tmux status bar theme"""
    return f'''# Prism Theme: {name}
# Add to ~/.tmux.conf

# Status bar colors
set -g status-style "bg={c['bg']},fg={c['fg']}"
set -g status-left-style "bg={c['accent']},fg={c['bg']}"
set -g status-right-style "bg={c['bg']},fg={c['muted']}"

# Window status
set -g window-status-style "bg={c['bg']},fg={c['muted']}"
set -g window-status-current-style "bg={c['selection_bg']},fg={c['accent']},bold"
set -g window-status-activity-style "bg={c['bg']},fg={c['yellow']}"

# Pane borders
set -g pane-border-style "fg={c['muted']}"
set -g pane-active-border-style "fg={c['accent']}"

# Message/command mode
set -g message-style "bg={c['selection_bg']},fg={c['fg']}"
set -g message-command-style "bg={c['selection_bg']},fg={c['accent']}"

# Copy mode
set -g mode-style "bg={c['selection_bg']},fg={c['fg']}"

# Clock
set -g clock-mode-colour "{c['accent']}"
'''

# ═══════════════════════════════════════════════════════════════════
# Main Generator
# ═══════════════════════════════════════════════════════════════════

def main():
    print("Prism Multi-Platform Theme Generator")
    print("=" * 50)
    
    if not THEMES_DIR.exists():
        print(f"Error: Themes directory not found: {THEMES_DIR}")
        return 1
    
    # Create all output directories
    platforms = [
        "alacritty", "kitty", "wezterm", "iterm2",
        "windows-terminal", "jetbrains", "zed", "helix",
        "bat", "starship", "tmux"
    ]
    
    for platform in platforms:
        (OUTPUT_BASE / platform).mkdir(parents=True, exist_ok=True)
    
    theme_count = 0
    
    for theme_file in sorted(THEMES_DIR.glob("*.json")):
        try:
            with open(theme_file) as f:
                theme = json.load(f)
            
            name = theme_file.stem
            theme_type = theme.get("type", "dark")
            colors = get_terminal_colors(theme)
            theme_count += 1
            
            # Generate for each platform
            (OUTPUT_BASE / "alacritty" / f"{name}.toml").write_text(gen_alacritty(name, colors))
            (OUTPUT_BASE / "kitty" / f"{name}.conf").write_text(gen_kitty(name, colors))
            (OUTPUT_BASE / "wezterm" / f"{name}.toml").write_text(gen_wezterm(name, colors))
            (OUTPUT_BASE / "iterm2" / f"{name}.itermcolors").write_bytes(gen_iterm2(name, colors))
            (OUTPUT_BASE / "windows-terminal" / f"{name}.json").write_text(gen_windows_terminal(name, colors))
            (OUTPUT_BASE / "jetbrains" / f"Prism_{name}.icls").write_text(gen_jetbrains(name, colors, theme_type))
            (OUTPUT_BASE / "zed" / f"{name}.json").write_text(gen_zed(name, colors, theme_type))
            (OUTPUT_BASE / "helix" / f"prism-{name}.toml").write_text(gen_helix(name, colors, theme_type))
            (OUTPUT_BASE / "bat" / f"{name}.tmTheme.json").write_text(gen_bat(name, colors))
            (OUTPUT_BASE / "starship" / f"{name}.toml").write_text(gen_starship(name, colors))
            (OUTPUT_BASE / "tmux" / f"{name}.conf").write_text(gen_tmux(name, colors))
            
            print(f"  ✓ {name}")
            
        except Exception as e:
            print(f"  ✗ {theme_file.name}: {e}")
    
    print("=" * 50)
    print(f"Generated {theme_count} themes for {len(platforms)} platforms")
    print(f"Total files: {theme_count * len(platforms)}")
    print(f"Output: {OUTPUT_BASE}")
    
    return 0

if __name__ == "__main__":
    exit(main())
