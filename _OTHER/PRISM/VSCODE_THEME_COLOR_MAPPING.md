# VS Code Theme Color Token Mapping Guide

This document maps VS Code/Cursor theme color tokens to specific UI elements you see in the interface.

## Top Menu Bar
- **Menu items** (File, Edit, View, etc.): `menubar.selectionForeground` (when selected) or `titleBar.activeForeground` (default)
- **Menu background**: `menu.background`
- **Menu text**: `menu.foreground`
- **Menu selected item**: `menu.selectionForeground`

## Side Panel (Extensions View)
- **Side panel background**: `sideBar.background`
- **Section headers** (INSTALLED, RECOMMENDED): `sideBarSectionHeader.foreground` (if exists) or `sideBar.foreground`
- **Extension names**: `list.activeSelectionForeground` (when selected) or `sideBar.foreground` (default)
- **Extension descriptions**: `descriptionForeground` (if exists) or `sideBar.foreground` with reduced opacity
- **Extension icons**: Not directly themed (they use their own colors)
- **Badge numbers** (like "21", "0"): `badge.foreground` (text) on `badge.background`
- **List hover background**: `list.hoverBackground`

## Tabs
- **Active tab text** (e.g., "Extension: Straylight Prism Generator X"): `tab.activeForeground`
- **Active tab background**: `tab.activeBackground`
- **Active tab underline**: `tab.activeBorder`
- **Inactive tab text** (e.g., "prism"): `tab.inactiveForeground`
- **Inactive tab background**: `tab.inactiveBackground`
- **Tab border**: `tab.border`

## Extension Detail View Tabs (DETAILS, FEATURES)
- **Active tab** (DETAILS): `panelTitle.activeForeground` with `panelTitle.activeBorder` underline
- **Inactive tab** (FEATURES): `panelTitle.inactiveForeground`
- **Panel background**: `panel.background`

## Buttons
- **Primary button** (Set Color Theme - green): `button.background` (bg) + `button.foreground` (text)
- **Secondary buttons** (Disable, Uninstall - gray): `button.secondaryBackground` (bg) + `button.secondaryForeground` (text)
- **Button hover**: `button.hoverBackground` or `button.secondaryHoverBackground`

## Extension Detail Content (Markdown)
- **Main heading** ("Prism Theme Generator"): `markup.heading` token (scope: `markup.heading`, `entity.name.section.markdown`) - typically uses `base0D` (Vivid/Link color)
- **Sub-headings** ("Color Selection", "Monitor Support", "Features"): Same as main heading - `markup.heading`
- **Body text** ("VSCode extension for generating..."): `editor.foreground` (default text color)
- **Bullet points** (•): Same as body text - `editor.foreground`
- **Punctuation** (colons, parentheses, hyphens, slashes): `punctuation` token (scope: `punctuation`) - typically uses `base05` (Text color) or `base04` (Muted)
- **Descriptive text** (under bullet points, like "(background tint)"): `descriptionForeground` or `editor.foreground` with reduced opacity
- **Bold text**: `markup.bold` token (fontStyle: bold, inherits foreground)
- **Italic text**: `markup.italic` token (fontStyle: italic, inherits foreground)
- **Links**: `markup.underline.link` token (scope: `markup.underline.link`) - typically uses `base0C` (Bright/Info color)
- **Inline code**: `markup.inline.raw` token (scope: `markup.inline.raw`) - typically uses `base0B` (Vibrant/String color)

## Chat Panel (Right Side)
- **Chat background**: `panel.background`
- **Chat text** (user messages): `editor.foreground`
- **Chat text** (assistant replies): `editor.foreground` (same as user)
- **Input box background**: `input.background`
- **Input box text**: `input.foreground`
- **Input placeholder**: `input.placeholderForeground`

## General UI Elements
- **Foreground** (default text): `foreground` (global) or `editor.foreground` (editor-specific)
- **Description/secondary text**: `descriptionForeground` (if exists in theme, otherwise falls back to muted colors)
- **Focus border**: `focusBorder`
- **Selection background**: `selection.background`
- **Error text**: `errorForeground`
- **Warning text**: Uses warning colors from base09

## Important Notes

1. **Not all tokens may exist in every theme file** - Some themes may be missing certain tokens. If a token doesn't exist, VS Code will fall back to a default color or inherit from a parent token.

2. **Extension marketplace UI** uses standard workbench colors:
   - Extension list items use `list.*` tokens
   - Extension detail view uses `panel.*` tokens
   - Markdown content uses `markup.*` token scopes

3. **Token Colors vs Workbench Colors**:
   - `colors` section = Workbench UI colors (menus, panels, buttons, etc.)
   - `tokenColors` section = Syntax highlighting colors (markdown headings, code tokens, etc.)

4. **To add missing tokens**: Edit the theme JSON file and add the token to the `colors` section. VS Code will use it if it's defined.

## Base16 Color Roles (for reference)
- `base00`: Background (main editor canvas)
- `base01`: Surface (panels, sidebars)
- `base02`: Selection (highlighted regions)
- `base03`: Comments (de-emphasized text)
- `base04`: Muted (punctuation, brackets)
- `base05`: Text (primary content)
- `base06`: Bright (emphasized text)
- `base07`: Brightest (maximum contrast)
- `base08`: Deep (tags, deletions, errors)
- `base09`: Rich (numbers, constants, warnings)
- `base0A`: Hero (types, classes, accent)
- `base0B`: Vibrant (strings, additions, success)
- `base0C`: Bright (parameters, info, links)
- `base0D`: Vivid (functions, links, headings)
- `base0E`: Luminous (keywords, control)
- `base0F`: Subtle (deprecated, embedded)

## How to Modify

When you want to change a color:
1. Identify which UI element you want to change
2. Find the corresponding token name above
3. Edit the theme JSON file and change the color value for that token
4. The theme file structure is: `vscode-prism/vscode-prism-theme-generator/themes/prism-{theme-name}.json`

Example: To change the extension names in the sidebar, modify `sideBar.foreground` or `list.foreground` in the `colors` section of the theme JSON.
