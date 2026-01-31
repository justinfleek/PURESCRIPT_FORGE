# Prism Theme Generator - Plugin Integration Architecture

## Overview

This document describes how to integrate the Prism color science backend and luxury themes into all three editor plugins: VSCode, Neovim, and Emacs.

## Architecture Layers

```
┌─────────────────────────────────────────────────────────────────┐
│                        USER INTERFACE                           │
├─────────────────┬─────────────────────┬─────────────────────────┤
│    VSCode       │      Neovim         │        Emacs            │
│   Webview UI    │    Lua/Telescope    │      Custom Buffer      │
│   (HTML/CSS/JS) │    Float Windows    │      or Hydra Menu      │
├─────────────────┴─────────────────────┴─────────────────────────┤
│                     EFFECTS LAYER                               │
├─────────────────┬─────────────────────┬─────────────────────────┤
│  Full CSS/JS    │  Terminal-safe      │   GUI: Full effects     │
│  micro-effects  │  approximations     │   TTY: Colors only      │
├─────────────────┴─────────────────────┴─────────────────────────┤
│                   THEME GENERATION                              │
│              prism-theme-generator binary                       │
│              (Haskell with OKLCH color science)                 │
├─────────────────────────────────────────────────────────────────┤
│                    PRESET LIBRARY                               │
│              luxury-presets.json + presets.json                 │
└─────────────────────────────────────────────────────────────────┘
```

## VSCode Integration

### 1. Directory Structure
```
vscode-prism-theme-generator/
├── src/
│   ├── extension.ts           # Extension entry point
│   ├── ffiBridge.ts           # Calls Haskell binary (DONE)
│   ├── themeGeneratorPanel.ts # Main UI panel
│   ├── presetGallery.ts       # NEW: Preset browser
│   ├── themeInstaller.ts      # NEW: Install to VS Code
│   ├── microEffects.ts        # NEW: Webview effects
│   └── types.ts               # Type definitions
├── media/
│   ├── themeGenerator.css     # Base styles
│   ├── luxury.css             # NEW: Luxury effect styles
│   └── micro-interactions.js  # NEW: Effect engine
├── presets/
│   ├── luxury-presets.json    # Imported from prism-color-core
│   └── presets.json           # Imported from prism-color-core
└── bin/
    └── prism-theme-generator  # Bundled binary (or installed via npm postinstall)
```

### 2. Key Files to Create/Modify

#### presetGallery.ts - Preset Browser
```typescript
// Renders a beautiful gallery of preset themes in the webview
// Users can browse by category, see live previews, click to apply
```

#### themeInstaller.ts - Actually Apply Themes
```typescript
// Writes theme JSON to VS Code's theme directory
// Updates settings.json to use the new theme
// Handles theme switching without restart
```

#### micro-interactions.js - Webview Effects
```typescript
// Imported from prism-color-core/effects/micro-interactions.ts
// Compiled for browser, runs in webview
// Effects: cursor spotlight, hover lift, particles, etc.
```

### 3. Webview HTML Updates

Add to themeGeneratorPanel.ts `_getHtmlForWebview`:

```html
<!-- Luxury effects container -->
<div id="effects-layer" class="effects-layer">
  <div id="cursor-spotlight"></div>
  <div id="ambient-particles"></div>
</div>

<!-- Preset Gallery Section -->
<div class="section preset-gallery">
  <h2>Premium Presets</h2>
  <div class="category-tabs">
    <button data-category="luxury">🏛️ Luxury Marble</button>
    <button data-category="glass">💎 Glassmorphism</button>
    <button data-category="bento">📦 Bento</button>
    <button data-category="neumorphism">🫧 Neumorphism</button>
    <button data-category="responsive">✨ Responsive</button>
  </div>
  <div id="preset-grid" class="preset-grid"></div>
</div>

<!-- Effect Controls -->
<div class="section effects-controls">
  <h2>Micro-Interactions</h2>
  <label>
    <input type="checkbox" id="enableEffects" checked>
    Enable subtle effects
  </label>
  <div class="effect-sliders">
    <label>Glow Intensity: <input type="range" id="glowIntensity" min="0" max="100" value="8"></label>
    <label>Particle Count: <input type="range" id="particleCount" min="0" max="12" value="4"></label>
  </div>
</div>
```

---

## Neovim Integration

### 1. Directory Structure
```
nvim-prism/
├── lua/
│   └── prism/
│       ├── init.lua           # Plugin entry point
│       ├── generator.lua      # Calls Haskell binary
│       ├── presets.lua        # Preset definitions
│       ├── palette.lua        # Color palette manipulation
│       ├── highlights.lua     # Highlight group definitions
│       ├── telescope.lua      # NEW: Telescope picker
│       └── effects.lua        # NEW: Terminal-safe effects
├── colors/
│   └── prism.lua              # Generated colorscheme
├── presets/
│   └── *.lua                  # Pre-generated preset colorschemes
└── bin/
    └── prism-theme-generator  # Binary
```

### 2. Key Components

#### generator.lua - Call Haskell Backend
```lua
local M = {}

function M.generate(config)
  local json = vim.fn.json_encode(config)
  local result = vim.fn.system({
    'prism-theme-generator', 'generate'
  }, json)
  return vim.fn.json_decode(result)
end

return M
```

#### effects.lua - Terminal-Safe Effects
```lua
-- Effects that work in terminal
local M = {}

-- Subtle cursor line glow using blend
function M.setup_cursor_glow(color, intensity)
  vim.api.nvim_set_hl(0, 'CursorLine', {
    bg = color,
    blend = math.floor(intensity * 100)  -- 0-100 blend
  })
end

-- Floating window with border styling (bento-like)
function M.create_floating_card(opts)
  local buf = vim.api.nvim_create_buf(false, true)
  local win = vim.api.nvim_open_win(buf, true, {
    relative = 'editor',
    width = opts.width or 60,
    height = opts.height or 20,
    col = opts.col or 10,
    row = opts.row or 5,
    style = 'minimal',
    border = opts.border or 'rounded',
  })
  -- Apply card-like styling
  vim.api.nvim_win_set_option(win, 'winblend', opts.blend or 10)
  return win, buf
end

-- Statusline shimmer effect (changes subtly over time)
function M.setup_statusline_shimmer(colors)
  local idx = 1
  local timer = vim.loop.new_timer()
  timer:start(0, 3000, vim.schedule_wrap(function()
    idx = (idx % #colors) + 1
    vim.api.nvim_set_hl(0, 'StatusLine', { bg = colors[idx] })
  end))
  return timer  -- Return for cleanup
end

return M
```

#### telescope.lua - Preset Picker
```lua
local pickers = require('telescope.pickers')
local finders = require('telescope.finders')
local conf = require('telescope.config').values
local actions = require('telescope.actions')
local presets = require('prism.presets')

local M = {}

function M.preset_picker(opts)
  opts = opts or {}
  pickers.new(opts, {
    prompt_title = '🎨 Prism Premium Themes',
    finder = finders.new_table({
      results = presets.get_all(),
      entry_maker = function(preset)
        return {
          value = preset,
          display = preset.name .. ' - ' .. preset.inspiration,
          ordinal = preset.name .. preset.category,
        }
      end
    }),
    sorter = conf.generic_sorter(opts),
    previewer = require('prism.previewer').new(),  -- Live preview!
    attach_mappings = function(prompt_bufnr, map)
      actions.select_default:replace(function()
        actions.close(prompt_bufnr)
        local selection = actions.get_selected_entry()
        require('prism').apply_preset(selection.value)
      end)
      return true
    end,
  }):find()
end

return M
```

### 3. Highlight Groups Generation

The Haskell backend generates Base16 colors. Map them to Neovim highlight groups:

```lua
-- highlights.lua
local function apply_base16(colors)
  local hl = vim.api.nvim_set_hl
  
  -- Editor UI
  hl(0, 'Normal', { fg = colors.base05, bg = colors.base00 })
  hl(0, 'NormalFloat', { fg = colors.base05, bg = colors.base01 })
  hl(0, 'CursorLine', { bg = colors.base01 })
  hl(0, 'Visual', { bg = colors.base02 })
  hl(0, 'LineNr', { fg = colors.base03 })
  hl(0, 'CursorLineNr', { fg = colors.base0A, bold = true })
  
  -- Syntax
  hl(0, 'Comment', { fg = colors.base03, italic = true })
  hl(0, 'Constant', { fg = colors.base09 })
  hl(0, 'String', { fg = colors.base0B })
  hl(0, 'Function', { fg = colors.base0D })
  hl(0, 'Keyword', { fg = colors.base0E })
  hl(0, 'Type', { fg = colors.base0A })  -- Hero color!
  hl(0, 'Special', { fg = colors.base0C })
  hl(0, 'Error', { fg = colors.base08 })
  
  -- Treesitter (if available)
  hl(0, '@variable', { fg = colors.base05 })
  hl(0, '@function', { fg = colors.base0D })
  hl(0, '@keyword', { fg = colors.base0E })
  hl(0, '@string', { fg = colors.base0B })
  hl(0, '@type', { fg = colors.base0A })
  -- ... etc
end
```

---

## Emacs Integration

### 1. Directory Structure
```
emacs-prism/
├── prism.el                   # Main package
├── prism-generator.el         # Calls Haskell binary
├── prism-presets.el           # Preset definitions
├── prism-faces.el             # Face definitions
├── prism-modeline.el          # Custom mode-line
├── themes/
│   └── prism-*.el             # Generated theme files
└── bin/
    └── prism-theme-generator  # Binary
```

### 2. Key Components

#### prism-generator.el
```elisp
;;; prism-generator.el --- Generate themes via Haskell backend

(defun prism-generate-theme (config)
  "Generate theme by calling prism-theme-generator binary."
  (let* ((json-input (json-encode config))
         (result (with-temp-buffer
                   (call-process-region 
                    json-input nil
                    "prism-theme-generator" nil t nil
                    "generate")
                   (buffer-string))))
    (json-read-from-string result)))
```

#### prism-faces.el - Face Definitions
```elisp
;;; prism-faces.el --- Apply Base16 colors to Emacs faces

(defun prism-apply-base16 (colors)
  "Apply Base16 COLORS to Emacs faces."
  (let ((base00 (plist-get colors :base00))
        (base01 (plist-get colors :base01))
        (base02 (plist-get colors :base02))
        (base03 (plist-get colors :base03))
        (base04 (plist-get colors :base04))
        (base05 (plist-get colors :base05))
        (base06 (plist-get colors :base06))
        (base07 (plist-get colors :base07))
        (base08 (plist-get colors :base08))
        (base09 (plist-get colors :base09))
        (base0A (plist-get colors :base0A))
        (base0B (plist-get colors :base0B))
        (base0C (plist-get colors :base0C))
        (base0D (plist-get colors :base0D))
        (base0E (plist-get colors :base0E))
        (base0F (plist-get colors :base0F)))
    
    ;; Basic faces
    (set-face-attribute 'default nil :background base00 :foreground base05)
    (set-face-attribute 'cursor nil :background base0A)
    (set-face-attribute 'region nil :background base02)
    (set-face-attribute 'highlight nil :background base01)
    (set-face-attribute 'fringe nil :background base00)
    (set-face-attribute 'line-number nil :foreground base03)
    (set-face-attribute 'line-number-current-line nil :foreground base0A)
    
    ;; Font-lock faces (syntax highlighting)
    (set-face-attribute 'font-lock-comment-face nil :foreground base03 :slant 'italic)
    (set-face-attribute 'font-lock-string-face nil :foreground base0B)
    (set-face-attribute 'font-lock-keyword-face nil :foreground base0E)
    (set-face-attribute 'font-lock-function-name-face nil :foreground base0D)
    (set-face-attribute 'font-lock-variable-name-face nil :foreground base05)
    (set-face-attribute 'font-lock-type-face nil :foreground base0A)  ; Hero!
    (set-face-attribute 'font-lock-constant-face nil :foreground base09)
    (set-face-attribute 'font-lock-builtin-face nil :foreground base0C)
    (set-face-attribute 'font-lock-warning-face nil :foreground base08)
    
    ;; Mode-line
    (set-face-attribute 'mode-line nil 
                        :background base01 
                        :foreground base05
                        :box `(:line-width 1 :color ,base02))
    (set-face-attribute 'mode-line-inactive nil 
                        :background base00 
                        :foreground base03)))
```

#### prism-modeline.el - Luxury Mode-line
```elisp
;;; prism-modeline.el --- Premium mode-line with subtle effects

(defun prism-modeline-setup (colors)
  "Setup a premium mode-line with COLORS."
  (let ((accent (plist-get colors :base0A)))
    ;; Add a subtle gold accent line at top of mode-line
    (set-face-attribute 'mode-line nil
                        :overline accent
                        :box nil)))

;; For GUI Emacs: add subtle effects
(when (display-graphic-p)
  ;; Subtle glow on active window mode-line
  (defun prism-pulse-modeline ()
    "Subtle pulse effect on mode-line."
    ;; Implementation using timers and face manipulation
    ))
```

---

## Effect Capabilities by Platform

| Effect | VSCode Webview | Neovim Terminal | Neovim GUI | Emacs TTY | Emacs GUI |
|--------|---------------|-----------------|------------|-----------|-----------|
| Cursor spotlight | ✅ Full | ❌ | ❌ | ❌ | ⚠️ Limited |
| Ambient particles | ✅ Full | ❌ | ❌ | ❌ | ❌ |
| Hover lift | ✅ Full | ⚠️ Float blend | ⚠️ Float blend | ❌ | ⚠️ Limited |
| Glass blur | ✅ Full | ⚠️ winblend | ⚠️ winblend | ❌ | ⚠️ alpha |
| Glow effects | ✅ Full | ⚠️ blend | ⚠️ blend | ❌ | ⚠️ box |
| Neumorphism | ✅ Full | ❌ | ❌ | ❌ | ❌ |
| Marble texture | ✅ Full | ❌ | ❌ | ❌ | ❌ |
| Colors | ✅ Full | ✅ True color | ✅ True color | ✅ 256 | ✅ Full |
| Easter eggs | ✅ Full | ⚠️ Keymap | ⚠️ Keymap | ⚠️ Keymap | ⚠️ Keymap |

**Legend:**
- ✅ Full support
- ⚠️ Partial/approximated
- ❌ Not possible

---

## Installation & Distribution

### Option 1: Bundled Binary
Include pre-compiled `prism-theme-generator` binary for each platform:
- `bin/prism-theme-generator-darwin-arm64`
- `bin/prism-theme-generator-darwin-x64`
- `bin/prism-theme-generator-linux-x64`
- `bin/prism-theme-generator-win-x64.exe`

### Option 2: npm/Cabal Install
```json
// package.json postinstall script
"scripts": {
  "postinstall": "cabal install prism-theme-generator --installdir=./bin"
}
```

### Option 3: Pure TypeScript Fallback
For users who can't run the binary, include a TypeScript port of the OKLCH color science. Won't have formal verification but will work everywhere.

---

## Next Steps

1. **Build Haskell binary** for all platforms
2. **Create VSCode preset gallery** with luxury themes
3. **Add micro-interactions** to VSCode webview
4. **Create Neovim Telescope picker** with live preview
5. **Create Emacs theme generator** with Hydra menu
6. **Write installation scripts** for each platform
7. **Test across all editors** and refine effects

---

## File Locations

- Haskell backend: `/home/claude/prism-color-core/haskell/`
- Luxury presets: `/home/claude/prism-color-core/themes/luxury-presets.json`
- Micro-interactions: `/home/claude/prism-color-core/effects/micro-interactions.ts`
- VSCode plugin: `/home/claude/vscode-prism/vscode-prism-theme-generator/`
