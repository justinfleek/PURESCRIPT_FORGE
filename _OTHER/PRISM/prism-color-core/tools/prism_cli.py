#!/usr/bin/env python3
"""
Prism CLI - Theme Installation & Management

Usage:
    prism install fleek --editor vscode,neovim --terminal alacritty
    prism list [--category luxury|glass|wild|classic|harmonious]
    prism preview <theme>
    prism info <theme>
    prism export <theme> --format vscode
    prism search <query>

Requirements: pip install rich typer

"""

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import List, Optional
from enum import Enum

try:
    import typer
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich.text import Text
    from rich.syntax import Syntax
    from rich import print as rprint
except ImportError:
    print("Installing dependencies...")
    subprocess.run([sys.executable, "-m", "pip", "install", "typer", "rich", "--break-system-packages", "-q"])
    import typer
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich.text import Text
    from rich.syntax import Syntax
    from rich import print as rprint

app = typer.Typer(
    name="prism",
    help="Prism Theme System - 40 OKLCH color science themes",
    add_completion=False
)
console = Console()

# ═══════════════════════════════════════════════════════════════════
# Configuration
# ═══════════════════════════════════════════════════════════════════

SCRIPT_DIR = Path(__file__).parent
PRISM_ROOT = SCRIPT_DIR.parent.parent
THEMES_DIR = PRISM_ROOT / "prism-code" / "themes"

# Platform directories
PLATFORMS = {
    "opencode": PRISM_ROOT / "opencode-prism" / "themes",
    "vscode": PRISM_ROOT / "prism-vscode-final" / "themes",
    "cursor": PRISM_ROOT / "cursor-prism" / "themes",
    "neovim": PRISM_ROOT / "nvim-prism",
    "emacs": PRISM_ROOT / "prism-emacs" / "themes",
    "alacritty": PRISM_ROOT / "terminal-themes" / "alacritty",
    "kitty": PRISM_ROOT / "terminal-themes" / "kitty",
    "wezterm": PRISM_ROOT / "terminal-themes" / "wezterm",
    "iterm2": PRISM_ROOT / "terminal-themes" / "iterm2",
    "windows-terminal": PRISM_ROOT / "terminal-themes" / "windows-terminal",
    "jetbrains": PRISM_ROOT / "terminal-themes" / "jetbrains",
    "zed": PRISM_ROOT / "terminal-themes" / "zed",
    "helix": PRISM_ROOT / "terminal-themes" / "helix",
}

# Installation targets
INSTALL_TARGETS = {
    "alacritty": Path.home() / ".config" / "alacritty" / "themes",
    "kitty": Path.home() / ".config" / "kitty" / "themes",
    "wezterm": Path.home() / ".config" / "wezterm" / "colors",
    "helix": Path.home() / ".config" / "helix" / "themes",
    "zed": Path.home() / ".config" / "zed" / "themes",
    "neovim": Path.home() / ".local" / "share" / "nvim" / "site" / "pack" / "prism" / "start" / "prism.nvim",
    "emacs": Path.home() / ".emacs.d" / "prism-themes",
}

# Theme categories
CATEGORIES = {
    "flagship": ["fleek", "fleek-light"],
    "luxury": ["nero-marquina", "midnight-sapphire", "obsidian-rose-gold", 
               "champagne-noir", "emerald-velvet", "diamond-dust"],
    "glass": ["aurora-glass", "zen-garden", "tide-pool", "porcelain-moon", "soft-charcoal"],
    "harmonious": ["ocean-depths", "forest-canopy", "lavender-dusk", 
                   "slate-and-gold", "ember-hearth", "constellation-map"],
    "wild": ["neon-nexus", "blood-moon", "vaporwave-sunset", "acid-rain",
             "ultraviolet", "holographic", "cyber-noir", "synthwave-84"],
    "classic": ["catppuccin-mocha", "dracula-pro", "gruvbox-material", "nord-aurora",
                "one-dark-pro", "ayu-mirage", "rose-pine", "night-owl", "cobalt2",
                "palenight", "vesper", "tokyo-night-bento", "moonlight-ii"]
}

# ═══════════════════════════════════════════════════════════════════
# Helper Functions
# ═══════════════════════════════════════════════════════════════════

def get_all_themes() -> List[str]:
    """Get list of all available themes"""
    if THEMES_DIR.exists():
        return sorted([f.stem for f in THEMES_DIR.glob("*.json")])
    return []

def get_theme_info(name: str) -> Optional[dict]:
    """Load theme JSON data"""
    theme_file = THEMES_DIR / f"{name}.json"
    if theme_file.exists():
        with open(theme_file) as f:
            return json.load(f)
    return None

def get_category(theme_name: str) -> str:
    """Get the category for a theme"""
    for cat, themes in CATEGORIES.items():
        if theme_name in themes:
            return cat
    return "unknown"

def hex_to_ansi(hex_color: str) -> str:
    """Convert hex to ANSI escape code for true color"""
    h = hex_color.lstrip('#')
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    return f"\033[38;2;{r};{g};{b}m"

def render_swatch(hex_color: str, width: int = 4) -> Text:
    """Create a colored swatch"""
    return Text("█" * width, style=f"bold {hex_color}")

# ═══════════════════════════════════════════════════════════════════
# Commands
# ═══════════════════════════════════════════════════════════════════

@app.command()
def list(
    category: Optional[str] = typer.Option(None, "--category", "-c", help="Filter by category"),
    verbose: bool = typer.Option(False, "--verbose", "-v", help="Show detailed info")
):
    """List all available themes"""
    themes = get_all_themes()
    
    if category:
        if category not in CATEGORIES:
            console.print(f"[red]Unknown category: {category}[/red]")
            console.print(f"Available: {', '.join(CATEGORIES.keys())}")
            raise typer.Exit(1)
        themes = [t for t in themes if t in CATEGORIES[category]]
    
    table = Table(title="Prism Themes", border_style="cyan")
    table.add_column("Theme", style="bold")
    table.add_column("Category")
    table.add_column("Type")
    if verbose:
        table.add_column("Background")
        table.add_column("Accent")
    
    for name in themes:
        info = get_theme_info(name)
        cat = get_category(name)
        theme_type = info.get("type", "dark") if info else "dark"
        
        row = [name, cat, theme_type]
        
        if verbose and info:
            colors = info.get("colors", {})
            bg = colors.get("background", "#1a1a1a")
            accent = colors.get("accent", "#00a0e4")
            row.extend([
                Text(f"{bg} ", style=f"on {bg}") + render_swatch(bg),
                Text(f"{accent} ") + render_swatch(accent)
            ])
        
        table.add_row(*row)
    
    console.print(table)
    console.print(f"\n[dim]Total: {len(themes)} themes[/dim]")

@app.command()
def info(theme: str):
    """Show detailed information about a theme"""
    data = get_theme_info(theme)
    if not data:
        console.print(f"[red]Theme not found: {theme}[/red]")
        raise typer.Exit(1)
    
    colors = data.get("colors", {})
    syntax = colors.get("syntax", {})
    
    console.print(Panel(
        f"[bold]{data.get('name', theme)}[/bold]\n"
        f"Type: {data.get('type', 'dark')}\n"
        f"Category: {get_category(theme)}",
        title="Theme Info",
        border_style="cyan"
    ))
    
    # Color palette
    table = Table(title="Color Palette", border_style="dim")
    table.add_column("Role")
    table.add_column("Hex")
    table.add_column("Swatch")
    
    palette = [
        ("Background", colors.get("background", "#1a1a1a")),
        ("Foreground", colors.get("text", "#e0e0e0")),
        ("Accent", colors.get("accent", "#00a0e4")),
        ("Keyword", syntax.get("keyword", "#ff79c6")),
        ("String", syntax.get("string", "#f1fa8c")),
        ("Function", syntax.get("function", "#50fa7b")),
        ("Comment", syntax.get("comment", "#6272a4")),
        ("Number", syntax.get("number", "#bd93f9")),
        ("Type", syntax.get("type", "#8be9fd")),
    ]
    
    for role, color in palette:
        table.add_row(role, color, render_swatch(color, 8))
    
    console.print(table)

@app.command()
def preview(theme: str):
    """Preview a theme with sample code"""
    data = get_theme_info(theme)
    if not data:
        console.print(f"[red]Theme not found: {theme}[/red]")
        raise typer.Exit(1)
    
    colors = data.get("colors", {})
    syntax = colors.get("syntax", {})
    bg = colors.get("background", "#1a1a1a")
    fg = colors.get("text", "#e0e0e0")
    
    # Sample code with inline styling
    code = f'''[bold {syntax.get("keyword", "#ff79c6")}]def[/] [bold {syntax.get("function", "#50fa7b")}]fibonacci[/]([{fg}]n[/]: [{syntax.get("type", "#8be9fd")}]int[/]) -> [{syntax.get("type", "#8be9fd")}]int[/]:
    [{syntax.get("comment", "#6272a4")} italic]# Calculate the nth Fibonacci number[/]
    [{syntax.get("keyword", "#ff79c6")}]if[/] [{fg}]n[/] <= [{syntax.get("number", "#bd93f9")}]1[/]:
        [{syntax.get("keyword", "#ff79c6")}]return[/] [{fg}]n[/]
    [{syntax.get("keyword", "#ff79c6")}]return[/] [bold {syntax.get("function", "#50fa7b")}]fibonacci[/]([{fg}]n[/] - [{syntax.get("number", "#bd93f9")}]1[/]) + [bold {syntax.get("function", "#50fa7b")}]fibonacci[/]([{fg}]n[/] - [{syntax.get("number", "#bd93f9")}]2[/])

[{syntax.get("comment", "#6272a4")} italic]# Main execution[/]
[{fg}]result[/] = [bold {syntax.get("function", "#50fa7b")}]fibonacci[/]([{syntax.get("number", "#bd93f9")}]10[/])
[bold {syntax.get("function", "#50fa7b")}]print[/]([{syntax.get("string", "#f1fa8c")}]f"Result: {{result}}"[/])'''
    
    console.print(Panel(
        code,
        title=f"Preview: {theme}",
        border_style=colors.get("accent", "cyan"),
        style=f"on {bg}"
    ))

@app.command()
def install(
    themes: List[str] = typer.Argument(..., help="Theme names to install (or 'all')"),
    editor: Optional[str] = typer.Option(None, "--editor", "-e", help="Editors: vscode,neovim,emacs"),
    terminal: Optional[str] = typer.Option(None, "--terminal", "-t", help="Terminals: alacritty,kitty,wezterm,helix"),
    dry_run: bool = typer.Option(False, "--dry-run", help="Show what would be installed")
):
    """Install themes to editors and terminals"""
    
    # Expand 'all'
    if "all" in themes:
        themes = get_all_themes()
    
    # Validate themes
    available = get_all_themes()
    for t in themes:
        if t not in available:
            console.print(f"[red]Theme not found: {t}[/red]")
            raise typer.Exit(1)
    
    # Parse targets
    editors = editor.split(",") if editor else []
    terminals = terminal.split(",") if terminal else []
    
    if not editors and not terminals:
        console.print("[yellow]No targets specified. Use --editor and/or --terminal[/yellow]")
        console.print("Examples:")
        console.print("  prism install fleek --editor vscode,neovim")
        console.print("  prism install all --terminal alacritty,kitty")
        raise typer.Exit(1)
    
    installed = []
    
    for target in editors + terminals:
        target = target.strip().lower()
        
        if target not in INSTALL_TARGETS:
            console.print(f"[yellow]Unknown target: {target}, skipping[/yellow]")
            continue
        
        source_dir = PLATFORMS.get(target)
        dest_dir = INSTALL_TARGETS[target]
        
        if not source_dir or not source_dir.exists():
            console.print(f"[yellow]Source not found for {target}, skipping[/yellow]")
            continue
        
        if dry_run:
            console.print(f"[dim]Would install to: {dest_dir}[/dim]")
            continue
        
        # Create destination
        dest_dir.mkdir(parents=True, exist_ok=True)
        
        # Copy themes
        for theme in themes:
            # Find the theme file
            patterns = [f"{theme}.*", f"prism-{theme}.*", f"prism-{theme.replace('-', '_')}.*"]
            copied = False
            
            for pattern in patterns:
                for src_file in source_dir.glob(pattern):
                    dst_file = dest_dir / src_file.name
                    shutil.copy2(src_file, dst_file)
                    installed.append((theme, target, dst_file))
                    copied = True
                    break
                if copied:
                    break
            
            if not copied and target == "neovim":
                # Neovim is a whole plugin, copy once
                if not (dest_dir / "lua").exists():
                    shutil.copytree(source_dir / "lua", dest_dir / "lua")
                    shutil.copytree(source_dir / "colors", dest_dir / "colors")
                    installed.append(("prism.nvim", target, dest_dir))
    
    if installed:
        table = Table(title="Installed", border_style="green")
        table.add_column("Theme")
        table.add_column("Target")
        table.add_column("Location")
        
        for theme, target, path in installed:
            table.add_row(theme, target, str(path))
        
        console.print(table)
    elif not dry_run:
        console.print("[yellow]No themes were installed[/yellow]")

@app.command()
def search(query: str):
    """Search for themes by name or description"""
    themes = get_all_themes()
    query_lower = query.lower()
    
    matches = []
    for name in themes:
        if query_lower in name.lower():
            matches.append(name)
            continue
        
        info = get_theme_info(name)
        if info:
            desc = info.get("description", "").lower()
            if query_lower in desc:
                matches.append(name)
    
    if matches:
        console.print(f"[green]Found {len(matches)} theme(s):[/green]")
        for m in matches:
            cat = get_category(m)
            console.print(f"  • [bold]{m}[/bold] [{cat}]")
    else:
        console.print(f"[yellow]No themes found matching '{query}'[/yellow]")

@app.command()
def export(
    theme: str,
    format: str = typer.Option("opencode", "--format", "-f", 
                               help="Format: opencode,vscode,alacritty,kitty,wezterm,windows-terminal,jetbrains,zed,helix"),
    output: Optional[Path] = typer.Option(None, "--output", "-o", help="Output file path")
):
    """Export a theme to a specific format"""
    data = get_theme_info(theme)
    if not data:
        console.print(f"[red]Theme not found: {theme}[/red]")
        raise typer.Exit(1)
    
    # Import the studio module for export functions
    from prism_studio import Theme, ThemeColors, ExportManager
    
    colors = data.get("colors", {})
    syntax = colors.get("syntax", {})
    
    tc = ThemeColors(
        background=colors.get("background", "#1a1a1a"),
        foreground=colors.get("text", "#e0e0e0"),
        muted=colors.get("textMuted", "#808080"),
        accent=colors.get("accent", "#00a0e4"),
        keyword=syntax.get("keyword", "#ff79c6"),
        string=syntax.get("string", "#f1fa8c"),
        function=syntax.get("function", "#50fa7b"),
        comment=syntax.get("comment", "#6272a4"),
        number=syntax.get("number", "#bd93f9"),
        type=syntax.get("type", "#8be9fd"),
    )
    
    t = Theme(name=theme, type=data.get("type", "dark"), colors=tc)
    
    exporters = {
        "opencode": ExportManager.to_opencode,
        "vscode": ExportManager.to_vscode,
        "alacritty": ExportManager.to_alacritty,
        "kitty": ExportManager.to_kitty,
        "wezterm": ExportManager.to_wezterm,
        "windows-terminal": ExportManager.to_windows_terminal,
        "jetbrains": ExportManager.to_jetbrains,
        "zed": ExportManager.to_zed,
        "helix": ExportManager.to_helix,
    }
    
    if format not in exporters:
        console.print(f"[red]Unknown format: {format}[/red]")
        console.print(f"Available: {', '.join(exporters.keys())}")
        raise typer.Exit(1)
    
    content = exporters[format](t)
    
    if output:
        output.write_text(content)
        console.print(f"[green]Exported to {output}[/green]")
    else:
        console.print(content)

@app.command()
def platforms():
    """List supported platforms and installation paths"""
    table = Table(title="Supported Platforms", border_style="cyan")
    table.add_column("Platform", style="bold")
    table.add_column("Type")
    table.add_column("Install Path")
    
    editors = ["opencode", "vscode", "cursor", "neovim", "emacs", "jetbrains", "zed", "helix"]
    terminals = ["alacritty", "kitty", "wezterm", "iterm2", "windows-terminal"]
    
    for p in editors:
        path = INSTALL_TARGETS.get(p, "Manual install")
        table.add_row(p, "Editor", str(path))
    
    for p in terminals:
        path = INSTALL_TARGETS.get(p, "Manual install")
        table.add_row(p, "Terminal", str(path))
    
    console.print(table)

if __name__ == "__main__":
    app()
