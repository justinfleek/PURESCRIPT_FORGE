#!/usr/bin/env python3
"""
PRISM Theme Creator
===================
Create a new theme from 5 colors.

Usage:
    python create_theme.py --name "My Theme" --bg "#1a1a1a" --accent "#ff5500" --fg "#ffffff" --comment "#666666" --hl "#252525" --type dark

Or edit the CUSTOM_THEMES dict below and run:
    python create_theme.py
"""

import json
import argparse
from pathlib import Path

# ============================================================================
# ADD YOUR CUSTOM THEMES HERE
# ============================================================================

CUSTOM_THEMES = {
    # "my_theme": {
    #     "name": "My Theme",
    #     "type": "dark",  # or "light"
    #     "bg": "#1a1a1a",
    #     "accent": "#ff5500",
    #     "fg": "#ffffff",
    #     "comment": "#666666",
    #     "hl": "#252525",
    # },
}

# ============================================================================
# GENERATOR (don't edit below unless you know what you're doing)
# ============================================================================

def lighten(h, f=0.2):
    h = h.lstrip('#')
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    return f"#{int(min(255, r + (255-r)*f)):02x}{int(min(255, g + (255-g)*f)):02x}{int(min(255, b + (255-b)*f)):02x}"

def darken(h, f=0.2):
    h = h.lstrip('#')
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    return f"#{int(r*(1-f)):02x}{int(g*(1-f)):02x}{int(b*(1-f)):02x}"

def generate_vscode_theme(name, bg, accent, fg, comment, hl, theme_type="dark"):
    is_dark = theme_type == "dark"
    return {
        "name": f"Prism {name}",
        "type": theme_type,
        "colors": {
            "editor.background": bg,
            "editor.foreground": fg,
            "editorLineNumber.foreground": comment,
            "editorLineNumber.activeForeground": fg,
            "editorCursor.foreground": accent,
            "editor.selectionBackground": f"{accent}40",
            "editor.selectionHighlightBackground": f"{accent}25",
            "editor.lineHighlightBackground": hl,
            "editorBracketMatch.background": f"{accent}30",
            "editorBracketMatch.border": accent,
            "sideBar.background": hl,
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
            "tab.inactiveBackground": hl,
            "tab.inactiveForeground": comment,
            "panel.background": bg,
            "panel.border": hl,
            "terminal.background": bg,
            "terminal.foreground": fg,
            "terminal.ansiBlack": bg if is_dark else fg,
            "terminal.ansiRed": darken(accent, 0.15) if is_dark else darken(accent, 0.15),
            "terminal.ansiGreen": lighten(accent, 0.1) if is_dark else lighten(accent, 0.1),
            "terminal.ansiYellow": lighten(comment, 0.2) if is_dark else comment,
            "terminal.ansiBlue": accent,
            "terminal.ansiMagenta": darken(accent, 0.25) if is_dark else darken(accent, 0.25),
            "terminal.ansiCyan": lighten(accent, 0.2) if is_dark else lighten(accent, 0.15),
            "terminal.ansiWhite": fg if is_dark else bg,
            "terminal.ansiBrightBlack": comment,
            "terminal.ansiBrightRed": accent,
            "terminal.ansiBrightGreen": lighten(accent, 0.2) if is_dark else lighten(accent, 0.15),
            "terminal.ansiBrightYellow": fg if is_dark else lighten(comment, 0.1),
            "terminal.ansiBrightBlue": lighten(accent, 0.15) if is_dark else lighten(accent, 0.1),
            "terminal.ansiBrightMagenta": darken(accent, 0.1),
            "terminal.ansiBrightCyan": lighten(accent, 0.3) if is_dark else lighten(accent, 0.25),
            "terminal.ansiBrightWhite": lighten(fg, 0.1) if is_dark else lighten(bg, 0.05),
            "button.background": accent,
            "button.foreground": bg,
            "input.background": bg,
            "input.foreground": fg,
            "input.border": hl,
            "focusBorder": accent,
        },
        "tokenColors": [
            {"scope": "comment", "settings": {"foreground": comment, "fontStyle": "italic"}},
            {"scope": ["keyword", "storage.type", "storage.modifier"], "settings": {"foreground": accent}},
            {"scope": "string", "settings": {"foreground": lighten(accent, 0.3) if is_dark else darken(accent, 0.15)}},
            {"scope": ["constant.numeric", "constant.language"], "settings": {"foreground": lighten(accent, 0.2) if is_dark else darken(accent, 0.1)}},
            {"scope": "variable", "settings": {"foreground": fg}},
            {"scope": ["entity.name.function", "support.function"], "settings": {"foreground": lighten(accent, 0.25) if is_dark else darken(accent, 0.05)}},
            {"scope": ["entity.name.type", "entity.name.class"], "settings": {"foreground": fg}},
            {"scope": "entity.name.tag", "settings": {"foreground": accent}},
            {"scope": "entity.other.attribute-name", "settings": {"foreground": lighten(accent, 0.15) if is_dark else darken(accent, 0.1)}},
            {"scope": "punctuation", "settings": {"foreground": comment}},
        ]
    }

def main():
    parser = argparse.ArgumentParser(description="Create a PRISM theme")
    parser.add_argument("--name", help="Theme name")
    parser.add_argument("--bg", help="Background color (hex)")
    parser.add_argument("--accent", help="Accent color (hex)")
    parser.add_argument("--fg", help="Foreground/text color (hex)")
    parser.add_argument("--comment", help="Comment/muted color (hex)")
    parser.add_argument("--hl", help="Highlight/selection background (hex)")
    parser.add_argument("--type", default="dark", choices=["dark", "light"], help="Theme type")
    parser.add_argument("--output", "-o", help="Output directory", default=".")
    
    args = parser.parse_args()
    
    themes_to_generate = []
    
    # From command line
    if args.name and args.bg and args.accent and args.fg and args.comment and args.hl:
        slug = args.name.lower().replace(" ", "_")
        themes_to_generate.append((slug, {
            "name": args.name,
            "type": args.type,
            "bg": args.bg,
            "accent": args.accent,
            "fg": args.fg,
            "comment": args.comment,
            "hl": args.hl,
        }))
    
    # From CUSTOM_THEMES dict
    for slug, t in CUSTOM_THEMES.items():
        themes_to_generate.append((slug, t))
    
    if not themes_to_generate:
        print("No themes to generate!")
        print("Either use command line args or add themes to CUSTOM_THEMES dict")
        print("\nExample:")
        print('  python create_theme.py --name "Ocean Blue" --bg "#0a1628" --accent "#00bcd4" --fg "#e0e0e0" --comment "#546e7a" --hl "#1a2a3a" --type dark')
        return
    
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    for slug, t in themes_to_generate:
        theme = generate_vscode_theme(
            t["name"], t["bg"], t["accent"], t["fg"], t["comment"], t["hl"], t.get("type", "dark")
        )
        
        filepath = output_dir / f"prism-{slug}.json"
        with open(filepath, 'w') as f:
            json.dump(theme, f, indent=2)
        
        print(f"Created: {filepath}")
        print(f"  Name: {theme['name']}")
        print(f"  Type: {theme['type']}")
        print(f"  Colors: bg={t['bg']} accent={t['accent']} fg={t['fg']}")
        print()

if __name__ == "__main__":
    main()
