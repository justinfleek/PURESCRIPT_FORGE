#!/bin/bash
#
# PRISM VSCode Extension Build Script
# ====================================
#
# VSCode THEME extensions are pure JSON - no compilation needed!
# This is different from regular extensions that need TypeScript.
#
# WHAT YOU NEED:
# 1. package.json - declares themes to VSCode
# 2. themes/*.json - the actual color definitions
# 3. media/icon.png - 128x128 icon
# 4. README.md - marketplace description
#
# THAT'S IT. No TypeScript, no webpack, no build step.
#

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║         PRISM VSCode Theme Extension Builder               ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Check for icon
if [ ! -f "media/icon.png" ]; then
    echo "⚠️  WARNING: media/icon.png is missing!"
    echo "   The marketplace requires a 128x128 PNG icon."
    echo "   Open prism-icon-generator.html to create one."
    echo ""
fi

# Check for vsce
if ! command -v vsce &> /dev/null; then
    echo "📦 Installing vsce (VS Code Extension tool)..."
    npm install -g @vscode/vsce
fi

# Verify themes exist
THEME_COUNT=$(ls themes/*.json 2>/dev/null | wc -l)
echo "✓ Found $THEME_COUNT theme files"

# Package the extension
echo ""
echo "📦 Packaging extension..."
vsce package

# Show result
VSIX=$(ls *.vsix 2>/dev/null | head -1)
if [ -n "$VSIX" ]; then
    echo ""
    echo "✅ SUCCESS! Created: $VSIX"
    echo ""
    echo "To install locally for testing:"
    echo "  code --install-extension $VSIX"
    echo ""
    echo "To publish to marketplace:"
    echo "  vsce login fleek-ai"
    echo "  vsce publish"
else
    echo "❌ Failed to create .vsix package"
    exit 1
fi
