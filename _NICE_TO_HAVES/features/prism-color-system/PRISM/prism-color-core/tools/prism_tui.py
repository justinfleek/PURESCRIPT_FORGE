#!/usr/bin/env python3
"""
Prism Theme Studio - Interactive TUI

A full-featured terminal UI for browsing, previewing, and validating
color themes with OKLCH color science.

Requirements: pip install textual rich

Usage:
    python prism_tui.py
    python prism_tui.py --themes-dir /path/to/themes
"""

import json
import math
import os
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.console import Console
from rich.style import Style
from rich.syntax import Syntax
from rich.text import Text
from rich.table import Table
from rich.panel import Panel

from textual.app import App, ComposeResult
from textual.containers import Container, Horizontal, Vertical, ScrollableContainer
from textual.widgets import (
    Header, Footer, Static, Button, ListView, ListItem, 
    Label, TabbedContent, TabPane, DataTable, Input
)
from textual.binding import Binding
from textual.reactive import reactive

# ═══════════════════════════════════════════════════════════════════
# Color Science (mirrors Lean4 verified implementations)
# ═══════════════════════════════════════════════════════════════════

def srgb_to_linear(c: float) -> float:
    """sRGB gamma expansion - verified in Lean4"""
    if c <= 0.04045:
        return c / 12.92
    return ((c + 0.055) / 1.055) ** 2.4

def linear_to_srgb(c: float) -> float:
    """sRGB gamma compression - verified in Lean4"""
    if c <= 0.0031308:
        return 12.92 * c
    return 1.055 * (c ** (1/2.4)) - 0.055

def relative_luminance(r: float, g: float, b: float) -> float:
    """WCAG relative luminance - verified in Lean4"""
    return 0.2126 * srgb_to_linear(r) + 0.7152 * srgb_to_linear(g) + 0.0722 * srgb_to_linear(b)

def contrast_ratio(l1: float, l2: float) -> float:
    """WCAG contrast ratio - proven ≥ 1 in Lean4"""
    lighter, darker = max(l1, l2), min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)

def hex_to_rgb(hex_color: str) -> Tuple[float, float, float]:
    """Parse hex to RGB floats [0,1]"""
    h = hex_color.lstrip('#')
    if len(h) == 3:
        h = ''.join(c*2 for c in h)
    return tuple(int(h[i:i+2], 16) / 255 for i in (0, 2, 4))

def rgb_to_hex(r: float, g: float, b: float) -> str:
    """RGB floats to hex"""
    return f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"

def wcag_rating(ratio: float) -> Tuple[str, str]:
    """Get WCAG level and color"""
    if ratio >= 7.0:
        return "AAA", "green"
    elif ratio >= 4.5:
        return "AA", "yellow"
    elif ratio >= 3.0:
        return "AA-LG", "dark_orange"
    else:
        return "FAIL", "red"

def oklch_to_srgb(l: float, c: float, h: float) -> Tuple[float, float, float]:
    """OKLCH to sRGB - full conversion chain"""
    h_rad = h * (math.pi / 180)
    a, b = c * math.cos(h_rad), c * math.sin(h_rad)
    
    l_ = l + 0.3963377774 * a + 0.2158037573 * b
    m_ = l - 0.1055613458 * a - 0.0638541728 * b
    s_ = l - 0.0894841775 * a - 1.2914855480 * b
    
    lms_l, lms_m, lms_s = l_**3, m_**3, s_**3
    
    x = 1.2270138511 * lms_l - 0.5577999807 * lms_m + 0.2812561490 * lms_s
    y = -0.0405801784 * lms_l + 1.1122568696 * lms_m - 0.0716766787 * lms_s
    z = -0.0763812845 * lms_l - 0.4214819784 * lms_m + 1.5861632204 * lms_s
    
    x, y, z = max(0, x), max(0, y), max(0, z)
    
    r = max(0, min(1, 3.2404542 * x - 1.5371385 * y - 0.4985314 * z))
    g = max(0, min(1, -0.9692660 * x + 1.8760108 * y + 0.0415560 * z))
    b = max(0, min(1, 0.0556434 * x - 0.2040259 * y + 1.0572252 * z))
    
    return (linear_to_srgb(r), linear_to_srgb(g), linear_to_srgb(b))

# ═══════════════════════════════════════════════════════════════════
# Theme Loading
# ═══════════════════════════════════════════════════════════════════

SAMPLE_CODE = '''def fibonacci(n: int) -> int:
    """Calculate the nth Fibonacci number."""
    if n <= 1:
        return n
    # Recursive case
    return fibonacci(n - 1) + fibonacci(n - 2)

class ThemeEngine:
    """OKLCH-based color theme generator."""
    
    def __init__(self, base_hue: float = 220.0):
        self.base_hue = base_hue
        self.palette = {}
    
    async def generate(self) -> dict:
        colors = await self._compute_palette()
        return {"name": "prism", "colors": colors}
    
    def _validate_contrast(self, fg: str, bg: str) -> bool:
        ratio = contrast_ratio(fg, bg)
        return ratio >= 4.5  # WCAG AA

# Usage
engine = ThemeEngine(base_hue=145)
theme = await engine.generate()
print(f"Generated: {theme['name']}")
'''

def load_themes(themes_dir: Path) -> Dict[str, dict]:
    """Load all themes from directory"""
    themes = {}
    if not themes_dir.exists():
        return themes
    
    for f in sorted(themes_dir.glob("*.json")):
        try:
            with open(f) as fp:
                theme = json.load(fp)
                themes[f.stem] = theme
        except:
            pass
    return themes

def get_theme_colors(theme: dict) -> dict:
    """Extract color mapping from theme"""
    colors = theme.get("colors", {})
    return {
        "bg": colors.get("background", "#1a1a1a"),
        "fg": colors.get("text", "#e0e0e0"),
        "muted": colors.get("textMuted", "#808080"),
        "accent": colors.get("accent", "#00a0e4"),
        "keyword": colors.get("syntax", {}).get("keyword", "#ff79c6"),
        "string": colors.get("syntax", {}).get("string", "#f1fa8c"),
        "function": colors.get("syntax", {}).get("function", "#50fa7b"),
        "comment": colors.get("syntax", {}).get("comment", "#6272a4"),
        "number": colors.get("syntax", {}).get("number", "#bd93f9"),
        "type": colors.get("syntax", {}).get("type", "#8be9fd"),
    }

# ═══════════════════════════════════════════════════════════════════
# TUI Components
# ═══════════════════════════════════════════════════════════════════

class ColorSwatch(Static):
    """Display a color swatch with hex value"""
    
    def __init__(self, color: str, label: str = "", **kwargs):
        super().__init__(**kwargs)
        self.color = color
        self.label = label
    
    def render(self):
        r, g, b = hex_to_rgb(self.color)
        lum = relative_luminance(r, g, b)
        text_color = "white" if lum < 0.5 else "black"
        
        text = Text()
        text.append("████ ", style=Style(color=self.color))
        text.append(f"{self.color} ", style=Style(color=self.color, bold=True))
        if self.label:
            text.append(f"({self.label})", style="dim")
        return text

class ContrastBadge(Static):
    """Display WCAG contrast rating"""
    
    def __init__(self, fg: str, bg: str, **kwargs):
        super().__init__(**kwargs)
        self.fg = fg
        self.bg = bg
    
    def render(self):
        fg_rgb = hex_to_rgb(self.fg)
        bg_rgb = hex_to_rgb(self.bg)
        fg_lum = relative_luminance(*fg_rgb)
        bg_lum = relative_luminance(*bg_rgb)
        ratio = contrast_ratio(fg_lum, bg_lum)
        rating, color = wcag_rating(ratio)
        
        text = Text()
        text.append(f"{ratio:.1f}:1 ", style="bold")
        text.append(f"[{rating}]", style=Style(color=color, bold=True))
        return text

class ThemePreview(Static):
    """Live syntax-highlighted code preview"""
    
    theme_name = reactive("")
    
    def __init__(self, themes: Dict[str, dict], **kwargs):
        super().__init__(**kwargs)
        self.themes = themes
        self._current_colors = {}
    
    def watch_theme_name(self, theme_name: str):
        if theme_name and theme_name in self.themes:
            self._current_colors = get_theme_colors(self.themes[theme_name])
            self.refresh()
    
    def render(self):
        if not self._current_colors:
            return Text("Select a theme to preview", style="dim italic")
        
        colors = self._current_colors
        console = Console(force_terminal=True, color_system="truecolor")
        
        # Build custom syntax theme
        text = Text()
        
        # Header
        text.append("─" * 60 + "\n", style=Style(color=colors["muted"]))
        
        # Simulate syntax highlighting
        lines = SAMPLE_CODE.split('\n')
        for line in lines:
            self._highlight_line(text, line, colors)
            text.append("\n")
        
        text.append("─" * 60, style=Style(color=colors["muted"]))
        
        return Panel(
            text,
            title=f"[bold]{self.theme_name}[/bold]",
            border_style=Style(color=colors["accent"]),
            style=Style(bgcolor=colors["bg"])
        )
    
    def _highlight_line(self, text: Text, line: str, colors: dict):
        """Simple syntax highlighting"""
        keywords = {'def', 'class', 'return', 'if', 'else', 'for', 'while', 'import', 
                   'from', 'async', 'await', 'with', 'as', 'try', 'except', 'raise'}
        builtins = {'int', 'str', 'float', 'bool', 'dict', 'list', 'print', 'True', 'False', 'None'}
        
        i = 0
        while i < len(line):
            # Comments
            if line[i] == '#':
                text.append(line[i:], style=Style(color=colors["comment"], italic=True))
                return
            
            # Strings
            if line[i] in '"\'':
                quote = line[i]
                # Check for triple quotes
                if line[i:i+3] in ('"""', "'''"):
                    end = line.find(line[i:i+3], i+3)
                    if end == -1:
                        end = len(line)
                    else:
                        end += 3
                    text.append(line[i:end], style=Style(color=colors["string"]))
                    i = end
                    continue
                else:
                    end = line.find(quote, i+1)
                    if end == -1:
                        end = len(line)
                    else:
                        end += 1
                    text.append(line[i:end], style=Style(color=colors["string"]))
                    i = end
                    continue
            
            # Numbers
            if line[i].isdigit():
                j = i
                while j < len(line) and (line[j].isdigit() or line[j] == '.'):
                    j += 1
                text.append(line[i:j], style=Style(color=colors["number"]))
                i = j
                continue
            
            # Identifiers
            if line[i].isalpha() or line[i] == '_':
                j = i
                while j < len(line) and (line[j].isalnum() or line[j] == '_'):
                    j += 1
                word = line[i:j]
                
                if word in keywords:
                    text.append(word, style=Style(color=colors["keyword"], bold=True))
                elif word in builtins:
                    text.append(word, style=Style(color=colors["type"]))
                elif j < len(line) and line[j] == '(':
                    text.append(word, style=Style(color=colors["function"]))
                else:
                    text.append(word, style=Style(color=colors["fg"]))
                i = j
                continue
            
            # Operators and punctuation
            text.append(line[i], style=Style(color=colors["fg"]))
            i += 1

class PalettePanel(Static):
    """Display full color palette for a theme"""
    
    def __init__(self, themes: Dict[str, dict], **kwargs):
        super().__init__(**kwargs)
        self.themes = themes
        self.current_theme = ""
    
    def set_theme(self, theme_name: str):
        self.current_theme = theme_name
        self.refresh()
    
    def render(self):
        if not self.current_theme or self.current_theme not in self.themes:
            return Text("Select a theme", style="dim")
        
        theme = self.themes[self.current_theme]
        colors = get_theme_colors(theme)
        
        table = Table(title="Color Palette", border_style="dim")
        table.add_column("Role", style="bold")
        table.add_column("Color")
        table.add_column("Swatch")
        table.add_column("Contrast vs BG")
        
        bg_rgb = hex_to_rgb(colors["bg"])
        bg_lum = relative_luminance(*bg_rgb)
        
        for role, color in colors.items():
            if role == "bg":
                continue
            
            fg_rgb = hex_to_rgb(color)
            fg_lum = relative_luminance(*fg_rgb)
            ratio = contrast_ratio(fg_lum, bg_lum)
            rating, rating_color = wcag_rating(ratio)
            
            swatch = Text("████", style=Style(color=color))
            contrast_text = Text(f"{ratio:.1f}:1 [{rating}]", style=Style(color=rating_color))
            
            table.add_row(role, color, swatch, contrast_text)
        
        return table

class ThemeList(ListView):
    """Scrollable list of themes"""
    
    def __init__(self, themes: Dict[str, dict], **kwargs):
        super().__init__(**kwargs)
        self.themes = themes
    
    def compose(self) -> ComposeResult:
        for name in self.themes:
            theme = self.themes[name]
            category = theme.get("_prism", {}).get("category", "")
            label = f"{name}" + (f" [{category}]" if category else "")
            yield ListItem(Label(label), id=f"theme-{name}")

# ═══════════════════════════════════════════════════════════════════
# Main App
# ═══════════════════════════════════════════════════════════════════

class PrismStudio(App):
    """Prism Theme Studio - Interactive TUI"""
    
    CSS = """
    Screen {
        layout: horizontal;
    }
    
    #sidebar {
        width: 30;
        border: solid $accent;
        padding: 1;
    }
    
    #main {
        width: 1fr;
        padding: 1;
    }
    
    #preview-container {
        height: 1fr;
    }
    
    #palette-container {
        height: auto;
        max-height: 15;
    }
    
    ThemePreview {
        height: 100%;
    }
    
    .title {
        text-align: center;
        text-style: bold;
        color: $accent;
        padding: 1;
    }
    
    ListView {
        height: 1fr;
    }
    
    ListItem {
        padding: 0 1;
    }
    
    ListItem:hover {
        background: $surface;
    }
    
    ListView:focus > ListItem.--highlight {
        background: $accent;
    }
    
    TabPane {
        padding: 1;
    }
    
    DataTable {
        height: 100%;
    }
    
    #color-picker {
        height: auto;
        padding: 1;
    }
    
    Input {
        width: 20;
        margin: 1;
    }
    """
    
    BINDINGS = [
        Binding("q", "quit", "Quit"),
        Binding("j", "cursor_down", "Down", show=False),
        Binding("k", "cursor_up", "Up", show=False),
        Binding("enter", "select", "Select", show=False),
        Binding("e", "export", "Export"),
        Binding("a", "audit", "Audit All"),
        Binding("/", "search", "Search"),
    ]
    
    selected_theme = reactive("")
    
    def __init__(self, themes_dir: Path = None):
        super().__init__()
        
        # Find themes directory
        if themes_dir is None:
            # Try relative paths
            candidates = [
                Path(__file__).parent.parent.parent / "prism-code" / "themes",
                Path(__file__).parent.parent.parent / "opencode-prism" / "themes",
                Path.cwd() / "themes",
            ]
            for c in candidates:
                if c.exists():
                    themes_dir = c
                    break
        
        self.themes_dir = themes_dir or Path.cwd()
        self.themes = load_themes(self.themes_dir)
        
        if not self.themes:
            # Create a default theme for demo
            self.themes = {
                "demo-dark": {
                    "name": "Demo Dark",
                    "type": "dark",
                    "colors": {
                        "background": "#1a1a2e",
                        "text": "#eaeaea",
                        "textMuted": "#888888",
                        "accent": "#00d4ff",
                        "syntax": {
                            "keyword": "#ff79c6",
                            "string": "#f1fa8c",
                            "function": "#50fa7b",
                            "comment": "#6272a4",
                            "number": "#bd93f9",
                            "type": "#8be9fd"
                        }
                    }
                }
            }
    
    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)
        
        with Horizontal():
            with Vertical(id="sidebar"):
                yield Static("🎨 PRISM THEMES", classes="title")
                yield ThemeList(self.themes, id="theme-list")
            
            with Vertical(id="main"):
                with TabbedContent():
                    with TabPane("Preview", id="tab-preview"):
                        yield ThemePreview(self.themes, id="preview")
                        yield PalettePanel(self.themes, id="palette")
                    
                    with TabPane("Audit", id="tab-audit"):
                        yield DataTable(id="audit-table")
                    
                    with TabPane("OKLCH", id="tab-oklch"):
                        with Vertical(id="color-picker"):
                            yield Static("OKLCH Color Converter", classes="title")
                            with Horizontal():
                                yield Input(placeholder="L (0-1)", id="input-l")
                                yield Input(placeholder="C (0-0.4)", id="input-c")
                                yield Input(placeholder="H (0-360)", id="input-h")
                            yield Button("Convert to Hex", id="btn-convert")
                            yield Static("", id="oklch-result")
        
        yield Footer()
    
    def on_mount(self):
        # Set up audit table
        table = self.query_one("#audit-table", DataTable)
        table.add_columns("Theme", "BG", "FG", "Contrast", "WCAG", "Issues")
        self.run_audit()
        
        # Select first theme
        if self.themes:
            first = list(self.themes.keys())[0]
            self.selected_theme = first
    
    def on_list_view_selected(self, event: ListView.Selected):
        if event.item and event.item.id:
            theme_name = event.item.id.replace("theme-", "")
            self.selected_theme = theme_name
    
    def watch_selected_theme(self, theme_name: str):
        preview = self.query_one("#preview", ThemePreview)
        preview.theme_name = theme_name
        
        palette = self.query_one("#palette", PalettePanel)
        palette.set_theme(theme_name)
        
        self.title = f"Prism Studio - {theme_name}"
    
    def run_audit(self):
        """Audit all themes for WCAG compliance"""
        table = self.query_one("#audit-table", DataTable)
        table.clear()
        
        for name, theme in self.themes.items():
            colors = get_theme_colors(theme)
            bg_rgb = hex_to_rgb(colors["bg"])
            fg_rgb = hex_to_rgb(colors["fg"])
            
            bg_lum = relative_luminance(*bg_rgb)
            fg_lum = relative_luminance(*fg_rgb)
            ratio = contrast_ratio(fg_lum, bg_lum)
            rating, color = wcag_rating(ratio)
            
            # Count issues
            issues = []
            for role in ["muted", "comment"]:
                c = colors.get(role)
                if c:
                    c_rgb = hex_to_rgb(c)
                    c_lum = relative_luminance(*c_rgb)
                    c_ratio = contrast_ratio(c_lum, bg_lum)
                    if c_ratio < 3.0:
                        issues.append(role)
            
            issue_str = ", ".join(issues) if issues else "✓"
            
            table.add_row(
                name,
                colors["bg"],
                colors["fg"],
                f"{ratio:.1f}:1",
                rating,
                issue_str
            )
    
    def action_audit(self):
        """Switch to audit tab and refresh"""
        self.query_one(TabbedContent).active = "tab-audit"
        self.run_audit()
    
    def action_export(self):
        """Export current theme"""
        if self.selected_theme:
            self.notify(f"Export {self.selected_theme} - Feature coming soon!")
    
    def on_button_pressed(self, event: Button.Pressed):
        if event.button.id == "btn-convert":
            self.convert_oklch()
    
    def convert_oklch(self):
        """Convert OKLCH inputs to hex"""
        try:
            l = float(self.query_one("#input-l", Input).value or "0.5")
            c = float(self.query_one("#input-c", Input).value or "0.1")
            h = float(self.query_one("#input-h", Input).value or "220")
            
            r, g, b = oklch_to_srgb(l, c, h)
            hex_color = rgb_to_hex(r, g, b)
            
            result = self.query_one("#oklch-result", Static)
            text = Text()
            text.append(f"\nOKLCH({l}, {c}, {h}°) → ", style="bold")
            text.append(hex_color, style=Style(color=hex_color, bold=True))
            text.append("\n")
            text.append("████████████████", style=Style(color=hex_color))
            result.update(text)
            
        except ValueError as e:
            self.notify(f"Invalid input: {e}", severity="error")

def main():
    import argparse
    parser = argparse.ArgumentParser(description="Prism Theme Studio")
    parser.add_argument("--themes-dir", type=Path, help="Directory containing theme JSON files")
    args = parser.parse_args()
    
    app = PrismStudio(themes_dir=args.themes_dir)
    app.run()

if __name__ == "__main__":
    main()
