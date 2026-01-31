#!/bin/bash
#
# PRISM - Build All Plugins
# ==========================
# Builds and packages all editor plugins for distribution.
#
# Prerequisites:
#   - Node.js 20+
#   - npm
#
# Output:
#   - dist/prism-themes-vscode.vsix        (static theme pack)
#   - dist/prism-generator-vscode.vsix     (211° generator)
#   - dist/prism-themes-cursor.vsix        (Cursor IDE)
#   - nvim-prism/                          (ready to install)
#   - prism-emacs/                         (ready to install)
#   - opencode-prism/                      (ready to install)

set -e

echo "╔══════════════════════════════════════════════════════════════════╗"
echo "║                    PRISM Build System                            ║"
echo "║         Formally Verified Color Themes for Every Editor          ║"
echo "╚══════════════════════════════════════════════════════════════════╝"
echo ""

# Create dist directory
mkdir -p dist

# Check for vsce
if ! command -v vsce &> /dev/null; then
    echo "📦 Installing vsce (VS Code Extension tool)..."
    npm install -g @vscode/vsce
fi

# ============================================================================
# 1. VSCode Static Themes (prism-vscode-final)
# ============================================================================
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📦 Building: VSCode Static Themes"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

cd prism-vscode-final

# Verify icon exists
if [ ! -f "media/icon.png" ]; then
    echo "❌ ERROR: media/icon.png missing!"
    exit 1
fi

# Count themes
THEME_COUNT=$(ls themes/*.json 2>/dev/null | wc -l)
echo "✓ Found $THEME_COUNT themes"

# Package
vsce package -o ../dist/prism-themes-vscode.vsix
echo "✅ Created: dist/prism-themes-vscode.vsix"

cd ..

# ============================================================================
# 2. VSCode 211° Generator (vscode-prism-theme-generator)
# ============================================================================
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📦 Building: VSCode 211° Generator"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

cd vscode-prism/vscode-prism-theme-generator

# Install dependencies
echo "📥 Installing dependencies..."
npm install

# Compile TypeScript
echo "🔨 Compiling TypeScript..."
npm run compile

# Verify icon exists
if [ ! -f "media/icon.png" ]; then
    echo "❌ ERROR: media/icon.png missing!"
    exit 1
fi

# Package
vsce package -o ../../dist/prism-generator-vscode.vsix
echo "✅ Created: dist/prism-generator-vscode.vsix"

cd ../..

# ============================================================================
# 3. Cursor IDE (cursor-prism)
# ============================================================================
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📦 Building: Cursor IDE Themes"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

cd cursor-prism

# Verify icon exists
if [ ! -f "media/icon.png" ]; then
    echo "❌ ERROR: media/icon.png missing!"
    exit 1
fi

# Count themes
THEME_COUNT=$(ls themes/*.json 2>/dev/null | wc -l)
echo "✓ Found $THEME_COUNT themes"

# Package
vsce package -o ../dist/prism-themes-cursor.vsix
echo "✅ Created: dist/prism-themes-cursor.vsix"

cd ..

# ============================================================================
# 4. Neovim (nvim-prism) - No build needed, just verify
# ============================================================================
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✓ Neovim Plugin: nvim-prism/"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Ready for installation via lazy.nvim, packer, or vim-plug"
echo \"  Presets: $(grep -c '= { bg =' nvim-prism/lua/prism/presets.lua 2>/dev/null || echo 0)\"

# ============================================================================
# 5. Emacs (prism-emacs) - No build needed, just verify
# ============================================================================
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✓ Emacs Package: prism-emacs/"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Ready for installation via use-package or straight.el"
echo "  Themes: $(ls prism-emacs/themes/*.el 2>/dev/null | wc -l)"

# ============================================================================
# 6. OpenCode (opencode-prism) - No build needed, just verify
# ============================================================================
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✓ OpenCode Themes: opencode-prism/"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Run: cd opencode-prism && ./install.sh"
echo "  Themes: $(ls opencode-prism/themes/*.json 2>/dev/null | wc -l)"

# ============================================================================
# Summary
# ============================================================================
echo ""
echo "╔══════════════════════════════════════════════════════════════════╗"
echo "║                      BUILD COMPLETE                              ║"
echo "╚══════════════════════════════════════════════════════════════════╝"
echo ""
echo "📦 VSCode Extensions (dist/):"
ls -la dist/*.vsix 2>/dev/null | awk '{print "   " $NF " (" $5 " bytes)"}'
echo ""
echo "📁 Ready for Installation:"
echo "   nvim-prism/       - Neovim (lazy.nvim, packer)"
echo "   prism-emacs/      - Emacs (use-package, straight.el)"
echo "   opencode-prism/   - OpenCode (./install.sh)"
echo "   terminal-themes/  - Alacritty, Kitty, WezTerm, iTerm2, etc."
echo ""
echo "🚀 To install VSCode extension locally:"
echo "   code --install-extension dist/prism-themes-vscode.vsix"
echo "   code --install-extension dist/prism-generator-vscode.vsix"
echo ""
echo "🌐 To publish to VS Code Marketplace:"
echo "   cd prism-vscode-final && vsce publish"
echo "   cd vscode-prism/vscode-prism-theme-generator && vsce publish"
