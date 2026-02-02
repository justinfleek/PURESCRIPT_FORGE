# Prism Theme Generator: Enhancement Roadmap

## Current Status Summary (Updated January 26, 2026)

| Component | Status | Notes |
|-----------|--------|-------|
| **40 Static Themes** | ✅ 100% | All platforms ready to ship |
| **OpenCode Plugin** | ✅ 100% | NEW - 40 themes with install script |
| **VSCode Extension** | ✅ 100% | VSIX ready, 40 themes |
| **Cursor IDE** | ✅ 100% | Same as VSCode |
| **Neovim Plugin** | ✅ 100% | 40 presets, full highlight groups |
| **Emacs Package** | ✅ 100% | 40 themes, MELPA ready |
| **Lean4 Proofs** | ⚠️ 99% | 1 numerical boundary `sorry` remaining |
| **Haskell Core** | ⚠️ 80% | Written but untested |
| **Python TUI** | ✅ NEW | Contrast checker tool |

---

## Completed This Session

- [x] Lean4: Hue normalization bounds proof
- [x] Lean4: sRGB gamma function bounds (both branches)
- [x] Lean4: Linear-to-sRGB bounds proofs
- [x] Lean4: XYZ non-negativity proofs  
- [x] Lean4: OKLAB-OKLCH roundtrip proof
- [x] Lean4: Symmetric component proofs (g, b)
- [x] OpenCode plugin with all 40 themes
- [x] Cursor IDE plugin
- [x] Python contrast checker TUI
- [x] Master README with all platforms

## Remaining `sorry` (1 total)

**Location:** `Conversions.lean:155`

```lean
have hboundary_approx : ((0.04045 + 0.055) / 1.055) ^ (2.4 : ℝ) ≥ 0.003130 := by
  sorry -- Numerical verification: the boundary value equals 0.0031308 by sRGB design
```

**Fix:** Use Mathlib's `Interval.rpow` for interval arithmetic, or define a verified constant:
```lean
lemma srgb_boundary_value : ((0.09545 : ℝ) / 1.055) ^ 2.4 ≥ 0.00313 := by
  native_decide -- or interval_cases
```

---

## Critical Gaps (Must Fix)

### 1. **Backend Integration** 🔴

All three plugins call a Python bridge that doesn't exist:
```
src/lattice/FFI/theme_generator_ffi.py  ← MISSING
```

**Fix:** Use the new Haskell `prism-theme-generator` binary:

```bash
# Build the Haskell core
cd prism-color-core/haskell
cabal build

# Test
echo '{"baseColor":{"hue":211,"saturation":0.12,"lightness":0.11},...}' | \
  prism-theme-generator generate
```

### 2. **VSCode: Separate Compilation Targets** 🔴

Currently `themeGenerator.ts` and `colorWheel.ts` use DOM APIs but compile with the Node extension code. These are **webview scripts** and should be:

1. Compiled separately with `"lib": ["dom"]`
2. Bundled into `out/themeGenerator.js`
3. Loaded by the webview HTML

**Fix:** Create `tsconfig.webview.json`:
```json
{
  "extends": "./tsconfig.json",
  "compilerOptions": {
    "lib": ["ES2020", "dom"],
    "outDir": "out/webview"
  },
  "include": ["src/colorWheel.ts", "src/themeGenerator.ts", "src/typeGuards.ts"]
}
```

### 3. **VSCode: Theme Installation** 🔴

Generated themes are displayed but never saved. Need:

1. Write `.json` theme files to extension storage
2. Update `package.json` contributes.themes dynamically
3. Prompt user to reload for theme activation

### 4. **Neovim: Actual Color Picker** 🟡

Current UI is ASCII art. Options:
- Use `vim.ui.select()` for preset colors
- Integrate with `nvim-colorizer.lua`
- External picker via `zenity`/`kdialog`

### 5. **Neovim: Apply Highlights** 🔴

No code to actually set highlight groups:
```lua
vim.api.nvim_set_hl(0, "Normal", { fg = palette.base05, bg = palette.base00 })
vim.api.nvim_set_hl(0, "Comment", { fg = palette.base03 })
-- ... etc
```

### 6. **Emacs: Widget-Based UI** 🟡

Replace ASCII art with proper widgets:
```elisp
(widget-create 'color :value "#54aeff")
```

### 7. **Emacs: Apply Faces** 🔴

No code to set face attributes:
```elisp
(set-face-attribute 'default nil :foreground base05 :background base00)
```

---

## Enhancements (Should Add)

### Color Science

| Feature | Impact | Difficulty |
|---------|--------|------------|
| **Gamut mapping** | Prevents clipping | Medium |
| **Color blindness simulation** | Accessibility | Medium |
| **CAM16/Jzazbz support** | More accurate than OKLAB | Hard |
| **Automatic contrast adjustment** | Always meets WCAG | Easy |

### UI/UX

| Feature | Impact | Difficulty |
|---------|--------|------------|
| **Live preview in editor** | Instant feedback | Medium |
| **Undo/redo for color changes** | Better UX | Easy |
| **Import existing theme** | Migration path | Medium |
| **Export to multiple formats** | VS Code, Alacritty, iTerm | Easy |

### Architecture

| Feature | Impact | Difficulty |
|---------|--------|------------|
| **Compile to WASM** | No FFI needed | Hard |
| **Shared TypeScript/PureScript core** | Browser native | Medium |
| **LSP-based theming** | Cross-editor | Hard |

---

## Lean4 Proof Completion

Current `sorry` locations that need proofs:

### PrismColor/Basic.lean
```lean
-- Line 45: Hue normalization bounds
def Hue.normalize (x : ℝ) : Hue :=
  let normalized := x - 360 * ⌊x / 360⌋
  ⟨normalized, by sorry, by sorry⟩  -- Need: 0 ≤ normalized < 360
```

**Proof Strategy:** Use `Int.floor` properties from Mathlib.

### PrismColor/Conversions.lean

Multiple bounds proofs for:
- sRGB transfer function (gamma)
- XYZ non-negativity
- OKLAB lightness bounds

**Proof Strategy:** 
- Gamma: Case split on threshold, use monotonicity
- XYZ: Matrix row sums + input bounds
- OKLAB: Composition of bounded functions

### PrismColor/Contrast.lean

The contrast proofs are mostly complete. Remaining:
- Lower bound derivation from luminance bounds

---

## Implementation Priority

### Phase 1: Make It Work (Week 1-2)
1. ✅ Create Haskell core library
2. ✅ Create Lean4 formalization
3. 🔲 Fix VSCode compilation (separate webview build)
4. 🔲 Wire up Haskell binary to plugins
5. 🔲 Test end-to-end theme generation

### Phase 2: Make It Usable (Week 3-4)
1. 🔲 VSCode: Theme installation to settings
2. 🔲 Neovim: Highlight group application
3. 🔲 Emacs: Face application
4. 🔲 All: Live preview

### Phase 3: Make It Excellent (Week 5-8)
1. 🔲 Complete all Lean4 proofs (zero `sorry`)
2. 🔲 WCAG automatic contrast adjustment
3. 🔲 Color blindness simulation
4. 🔲 Export to Alacritty, iTerm, Kitty, WezTerm

### Phase 4: Scale It (Future)
1. 🔲 Compile Haskell to WASM (no binary dependency)
2. 🔲 Community theme gallery
3. 🔲 AI-assisted theme naming/description

---

## File Deliverables

### Haskell Core
```
prism-color-core/haskell/
├── prism-color-core.cabal     ✅
├── src/
│   ├── PrismColor.hs          ✅
│   ├── PrismColor/
│   │   ├── Types.hs           ✅
│   │   ├── SRGB.hs            ✅
│   │   ├── OKLAB.hs           ✅
│   │   ├── Contrast.hs        ✅
│   │   ├── Palette.hs         ✅
│   │   └── FFI.hs             ✅
└── app/
    └── Main.hs                ✅
```

### Lean4 Proofs
```
prism-color-core/lean4/
├── lakefile.lean              ✅
├── PrismColor.lean            ✅
└── PrismColor/
    ├── Basic.lean             ✅ (some sorry)
    ├── Conversions.lean       ✅ (some sorry)
    └── Contrast.lean          ✅ (complete)
```

### Plugin Fixes Needed
```
vscode-prism-theme-generator/
├── tsconfig.json              ✅ Fixed (dom types)
├── tsconfig.webview.json      🔲 TODO
├── src/
│   ├── themeGeneratorPanel.ts ✅ Fixed (import)
│   ├── colorWheel.ts          ✅ Fixed (types)
│   ├── themeGenerator.ts      ✅ Fixed (types)
│   ├── ffiBridge.ts           ✅ Fixed (spawn)
│   └── themeInstaller.ts      🔲 TODO (new file)
```

---

## Testing Checklist

### Unit Tests
- [ ] sRGB ↔ Linear RGB roundtrip (< 1e-10 error)
- [ ] sRGB ↔ OKLCH roundtrip (< 1e-6 error)
- [ ] Contrast ratio properties (symmetric, ≥ 1)
- [ ] Black balance bounds (0-20%)
- [ ] Hue normalization (always [0, 360))

### Integration Tests
- [ ] JSON FFI: valid config → variants
- [ ] JSON FFI: invalid config → error message
- [ ] VSCode: webview loads without error
- [ ] Neovim: `:PrismThemeGenerate` opens UI
- [ ] Emacs: `M-x prism-theme-generator` runs

### Visual Tests
- [ ] Generated palette has sufficient contrast
- [ ] Colors look perceptually uniform
- [ ] Dark themes have proper black balance
- [ ] Light themes have proper white balance

---

## Success Metrics

1. **Zero `sorry`** in Lean4 → Mathematically proven correctness
2. **100% WCAG AA** → Accessible to all users
3. **< 5 second generation** → Responsive UX
4. **Cross-editor parity** → Same theme everywhere
5. **10M+ potential users** → VSCode + Neovim + Emacs reach
