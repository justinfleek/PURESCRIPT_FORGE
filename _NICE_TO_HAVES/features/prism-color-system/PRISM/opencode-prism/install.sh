#!/bin/bash
# Prism Themes for OpenCode - Installation Script
# https://github.com/weylai/prism-themes

set -e

THEMES_DIR="${XDG_CONFIG_HOME:-$HOME/.config}/opencode/themes"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "🎨 Prism Themes for OpenCode - Installer"
echo "========================================="
echo

# Create themes directory
mkdir -p "$THEMES_DIR"

# Copy themes
echo "Installing 40 themes to $THEMES_DIR..."
cp "$SCRIPT_DIR/themes/"*.json "$THEMES_DIR/"

# Count installed
COUNT=$(ls "$THEMES_DIR"/*.json 2>/dev/null | wc -l)

echo
echo "✅ Installed $COUNT Prism themes!"
echo
echo "To use a theme, run /theme in OpenCode and select one."
echo "Or add to your opencode.json:"
echo
echo '  {'
echo '    "tui": {'
echo '      "theme": "fleek"'
echo '    }'
echo '  }'
echo
echo "Featured themes:"
echo "  • fleek         - Official Fleek AI theme"
echo "  • nero-marquina - Luxury Italian marble"
echo "  • neon-nexus    - Cyberpunk neon"
echo "  • catppuccin-mocha - Classic reimagined"
echo
echo "Enjoy! 🚀"
