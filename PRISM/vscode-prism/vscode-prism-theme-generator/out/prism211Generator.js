"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.Prism211GeneratorPanel = exports.SEMANTIC_COLORS = void 0;
exports.generateMonochromaticPalette = generateMonochromaticPalette;
const vscode = __importStar(require("vscode"));
const prismColor_1 = require("./prismColor");
// All colors share the SAME hue - only L and C vary
// This is the core insight: semantic hierarchy through lightness, not hue chaos
exports.SEMANTIC_COLORS = [
    // BACKGROUNDS (base00-03)
    // Near-zero chroma creates depth without distraction. Your code is the star, not the background.
    { id: "base00", name: "Background", description: "Main editor canvas", why: "L=0: Maximum depth. Minimal chroma keeps focus on code, not walls.", lightnessTarget: { dark: 0.0, light: 0.98 }, chromaMultiplier: 0.08, role: "background" },
    { id: "base01", name: "Surface", description: "Panels, sidebars", why: "L+12%: Subtle elevation creates visual layers without hard borders.", lightnessTarget: { dark: 0.12, light: 0.94 }, chromaMultiplier: 0.10, role: "background" },
    { id: "base02", name: "Selection", description: "Highlighted regions", why: "L+18%: Clear selection feedback. Must be visible but not jarring.", lightnessTarget: { dark: 0.18, light: 0.88 }, chromaMultiplier: 0.12, role: "background" },
    { id: "base03", name: "Comments", description: "De-emphasized text", why: "L=45%: WCAG AA-large (3:1). Readable when needed, invisible when scanning.", lightnessTarget: { dark: 0.45, light: 0.55 }, chromaMultiplier: 0.15, role: "background" },
    // FOREGROUNDS (base04-07)
    // Near-neutral text maximizes readability. Slight hue tint maintains cohesion.
    { id: "base04", name: "Muted", description: "Punctuation, brackets", why: "L=55%: Structural syntax shouldn't compete with semantics.", lightnessTarget: { dark: 0.55, light: 0.45 }, chromaMultiplier: 0.08, role: "foreground" },
    { id: "base05", name: "Text", description: "Primary content", why: "L=80%: WCAG AA (4.5:1). Optimized for hours of reading.", lightnessTarget: { dark: 0.80, light: 0.25 }, chromaMultiplier: 0.06, role: "foreground" },
    { id: "base06", name: "Bright", description: "Emphasized text", why: "L=90%: Draws attention for important elements.", lightnessTarget: { dark: 0.90, light: 0.18 }, chromaMultiplier: 0.04, role: "foreground" },
    { id: "base07", name: "Brightest", description: "Maximum contrast", why: "L=97%: Reserved for critical UI elements only.", lightnessTarget: { dark: 0.97, light: 0.10 }, chromaMultiplier: 0.02, role: "foreground" },
    // ACCENTS (base08-0F)
    // Full chroma at your chosen hue. Lightness creates hierarchy within the accent family.
    { id: "base08", name: "Deep", description: "Tags, deletions", why: "L=55%: Darkest accent. Grounds the palette, used for destructive actions.", lightnessTarget: { dark: 0.55, light: 0.50 }, chromaMultiplier: 1.0, role: "accent" },
    { id: "base09", name: "Rich", description: "Numbers, constants", why: "L=62%: Immutable values get their own distinct shade.", lightnessTarget: { dark: 0.62, light: 0.45 }, chromaMultiplier: 0.95, role: "accent" },
    { id: "base0A", name: "Hero", description: "Types, classes", why: "L=70%: YOUR HERO. The defining color of your theme.", lightnessTarget: { dark: 0.70, light: 0.40 }, chromaMultiplier: 1.0, role: "accent" },
    { id: "base0B", name: "Vibrant", description: "Strings, additions", why: "L=75%: Literal values. Bright enough to scan quickly.", lightnessTarget: { dark: 0.75, light: 0.38 }, chromaMultiplier: 0.90, role: "accent" },
    { id: "base0C", name: "Bright", description: "Parameters, info", why: "L=78%: Function arguments. Contextual clarity.", lightnessTarget: { dark: 0.78, light: 0.35 }, chromaMultiplier: 0.85, role: "accent" },
    { id: "base0D", name: "Vivid", description: "Functions, links", why: "L=82%: Callable entities. High visibility for navigation.", lightnessTarget: { dark: 0.82, light: 0.32 }, chromaMultiplier: 0.88, role: "accent" },
    { id: "base0E", name: "Luminous", description: "Keywords, control", why: "L=85%: Language constructs. Maximum semantic weight.", lightnessTarget: { dark: 0.85, light: 0.30 }, chromaMultiplier: 0.92, role: "accent" },
    { id: "base0F", name: "Subtle", description: "Deprecated, embedded", why: "L=50%, C=40%: Low-priority. Visible but clearly secondary.", lightnessTarget: { dark: 0.50, light: 0.55 }, chromaMultiplier: 0.40, role: "accent" },
];
/**
 * Generate a MONOCHROMATIC palette from a single hue.
 * ALL colors share the same hue - only L (lightness) and C (chroma) vary.
 */
function generateMonochromaticPalette(config) {
    const { heroHue, heroChroma, mode, monitor } = config;
    // Base chroma for fully saturated accents (OKLCH max is ~0.37 for most hues)
    const maxChroma = 0.18 * heroChroma; // Scaled by user's chroma preference
    // Background base lightness
    let baseBgL;
    if (mode === "dark") {
        baseBgL = monitor === "oled" ? 0.0 : 0.10;
    }
    else {
        baseBgL = 0.98;
    }
    const colors = {};
    // Generate each color - ALL with the SAME hue
    for (const sc of exports.SEMANTIC_COLORS) {
        const targetL = mode === "dark" ? sc.lightnessTarget.dark : sc.lightnessTarget.light;
        // Adjust base lightness for OLED/LCD
        let finalL = targetL;
        if (sc.role === "background" && mode === "dark" && monitor === "oled") {
            // Push backgrounds darker for OLED
            finalL = Math.max(0, targetL - 0.05);
        }
        // Chroma based on role
        let finalC;
        if (sc.role === "accent") {
            finalC = maxChroma * sc.chromaMultiplier;
        }
        else {
            // Backgrounds and foregrounds get subtle tint of the hero hue
            finalC = maxChroma * sc.chromaMultiplier * 0.3;
        }
        const oklch = {
            L: Math.max(0, Math.min(1, finalL)),
            C: finalC,
            H: heroHue // SAME hue for ALL colors
        };
        let rgb = (0, prismColor_1.oklchToSrgb)(oklch);
        // Ensure contrast for text colors
        if (sc.role === "foreground" && sc.id !== "base04") {
            const bg = (0, prismColor_1.hexToSrgb)(colors.base00 || (0, prismColor_1.srgbToHex)((0, prismColor_1.oklchToSrgb)({ L: baseBgL, C: maxChroma * 0.08 * 0.3, H: heroHue })));
            const cr = (0, prismColor_1.contrastRatio)(rgb, bg);
            if (cr < 4.5) {
                const adjusted = (0, prismColor_1.adjustLightnessForContrast)(oklch, bg, 4.5, mode === "dark");
                if (adjusted) {
                    rgb = (0, prismColor_1.oklchToSrgb)(adjusted);
                }
            }
        }
        // Ensure contrast for accents
        if (sc.role === "accent") {
            const bg = (0, prismColor_1.hexToSrgb)(colors.base00 || (0, prismColor_1.srgbToHex)((0, prismColor_1.oklchToSrgb)({ L: baseBgL, C: maxChroma * 0.08 * 0.3, H: heroHue })));
            const cr = (0, prismColor_1.contrastRatio)(rgb, bg);
            if (cr < 3.0) {
                const adjusted = (0, prismColor_1.adjustLightnessForContrast)(oklch, bg, 3.0, mode === "dark");
                if (adjusted) {
                    rgb = (0, prismColor_1.oklchToSrgb)(adjusted);
                }
            }
        }
        colors[sc.id] = (0, prismColor_1.srgbToHex)(rgb);
    }
    // Calculate contrast ratios
    const bg = (0, prismColor_1.hexToSrgb)(colors.base00);
    const crText = (0, prismColor_1.contrastRatio)((0, prismColor_1.hexToSrgb)(colors.base05), bg);
    const crComment = (0, prismColor_1.contrastRatio)((0, prismColor_1.hexToSrgb)(colors.base03), bg);
    const crAccent = (0, prismColor_1.contrastRatio)((0, prismColor_1.hexToSrgb)(colors.base0A), bg);
    return {
        colors,
        contrast: {
            text: Math.round(crText * 100) / 100,
            comment: Math.round(crComment * 100) / 100,
            accent: Math.round(crAccent * 100) / 100,
            wcagVerified: (0, prismColor_1.wcagAA)(crText) && (0, prismColor_1.wcagAALarge)(crComment) && (0, prismColor_1.wcagAALarge)(crAccent),
        },
        config,
    };
}
// ============================================================================
// VSCODE WEBVIEW PANEL
// ============================================================================
class Prism211GeneratorPanel {
    static createOrShow(context) {
        const column = vscode.window.activeTextEditor?.viewColumn ?? vscode.ViewColumn.One;
        if (Prism211GeneratorPanel.currentPanel) {
            Prism211GeneratorPanel.currentPanel._panel.reveal(column);
            return;
        }
        const panel = vscode.window.createWebviewPanel(Prism211GeneratorPanel.viewType, "Prism 211° Generator", column, {
            enableScripts: true,
            retainContextWhenHidden: true,
            localResourceRoots: [
                vscode.Uri.joinPath(context.extensionUri, "media"),
                vscode.Uri.joinPath(context.extensionUri, "out")
            ]
        });
        Prism211GeneratorPanel.currentPanel = new Prism211GeneratorPanel(panel, context);
    }
    constructor(panel, context) {
        this._disposables = [];
        this._currentPalette = null;
        this._panel = panel;
        this._context = context;
        this._update();
        this._panel.onDidDispose(() => this.dispose(), null, this._disposables);
        this._panel.webview.onDidReceiveMessage(async (message) => {
            switch (message.command) {
                case "generate":
                    this._generatePalette(message.config);
                    break;
                case "updateColor":
                    this._updateColor(message.colorId, message.hex);
                    break;
                case "export":
                    await this._exportTheme(message.name, message.colors);
                    break;
                case "apply":
                    await this._applyTheme(message.name, message.colors);
                    break;
            }
        }, null, this._disposables);
    }
    _generatePalette(config) {
        this._currentPalette = generateMonochromaticPalette(config);
        this._panel.webview.postMessage({
            command: "paletteGenerated",
            palette: this._currentPalette,
        });
    }
    _updateColor(colorId, hex) {
        if (this._currentPalette) {
            this._currentPalette.colors[colorId] = hex;
            // Recalculate contrast if relevant colors changed
            if (["base00", "base03", "base05", "base0A"].includes(colorId)) {
                const bg = (0, prismColor_1.hexToSrgb)(this._currentPalette.colors.base00);
                const text = (0, prismColor_1.hexToSrgb)(this._currentPalette.colors.base05);
                const comment = (0, prismColor_1.hexToSrgb)(this._currentPalette.colors.base03);
                const accent = (0, prismColor_1.hexToSrgb)(this._currentPalette.colors.base0A);
                this._currentPalette.contrast = {
                    text: Math.round((0, prismColor_1.contrastRatio)(text, bg) * 100) / 100,
                    comment: Math.round((0, prismColor_1.contrastRatio)(comment, bg) * 100) / 100,
                    accent: Math.round((0, prismColor_1.contrastRatio)(accent, bg) * 100) / 100,
                    wcagVerified: (0, prismColor_1.wcagAA)((0, prismColor_1.contrastRatio)(text, bg)) &&
                        (0, prismColor_1.wcagAALarge)((0, prismColor_1.contrastRatio)(comment, bg)) &&
                        (0, prismColor_1.wcagAALarge)((0, prismColor_1.contrastRatio)(accent, bg)),
                };
                this._panel.webview.postMessage({
                    command: "contrastUpdated",
                    contrast: this._currentPalette.contrast,
                });
            }
        }
    }
    async _exportTheme(name, colors) {
        const theme = this._buildVSCodeTheme(name, colors);
        // Ask user where to save
        const uri = await vscode.window.showSaveDialog({
            defaultUri: vscode.Uri.file(`prism-${name.toLowerCase().replace(/\\s+/g, "_")}.json`),
            filters: { "JSON": ["json"] }
        });
        if (uri) {
            await vscode.workspace.fs.writeFile(uri, Buffer.from(JSON.stringify(theme, null, 2)));
            vscode.window.showInformationMessage(`Theme exported: ${uri.fsPath}`);
        }
    }
    async _applyTheme(name, colors) {
        const theme = this._buildVSCodeTheme(name, colors);
        // Save to extension's themes directory
        const themesDir = vscode.Uri.joinPath(this._context.extensionUri, "themes");
        const themeFile = vscode.Uri.joinPath(themesDir, `prism-custom-${Date.now()}.json`);
        try {
            await vscode.workspace.fs.createDirectory(themesDir);
        }
        catch {
            // Directory may already exist
        }
        await vscode.workspace.fs.writeFile(themeFile, Buffer.from(JSON.stringify(theme, null, 2)));
        // Update user settings to use this theme
        const config = vscode.workspace.getConfiguration();
        await config.update("workbench.colorTheme", `Prism ${name}`, vscode.ConfigurationTarget.Global);
        vscode.window.showInformationMessage(`Theme "${name}" applied! You may need to reload.`);
    }
    _buildVSCodeTheme(name, c) {
        return {
            name: `Prism ${name}`,
            type: "dark",
            colors: {
                "editor.background": c.base00,
                "editor.foreground": c.base05,
                "editorLineNumber.foreground": c.base03,
                "editorLineNumber.activeForeground": c.base05,
                "editorCursor.foreground": c.base0A,
                "editor.selectionBackground": c.base0A + "40",
                "editor.selectionHighlightBackground": c.base0A + "25",
                "editor.lineHighlightBackground": c.base01,
                "editorBracketMatch.background": c.base0A + "30",
                "editorBracketMatch.border": c.base0A,
                "sideBar.background": c.base01,
                "sideBar.foreground": c.base05,
                "activityBar.background": c.base00,
                "activityBar.foreground": c.base05,
                "activityBar.activeBorder": c.base0A,
                "activityBarBadge.background": c.base0A,
                "activityBarBadge.foreground": c.base00,
                "titleBar.activeBackground": c.base00,
                "titleBar.activeForeground": c.base05,
                "statusBar.background": c.base00,
                "statusBar.foreground": c.base03,
                "tab.activeBackground": c.base00,
                "tab.activeForeground": c.base05,
                "tab.activeBorder": c.base0A,
                "tab.inactiveBackground": c.base01,
                "tab.inactiveForeground": c.base03,
                "panel.background": c.base00,
                "panel.border": c.base01,
                "terminal.background": c.base00,
                "terminal.foreground": c.base05,
                "terminal.ansiBlack": c.base00,
                "terminal.ansiRed": c.base08,
                "terminal.ansiGreen": c.base0B,
                "terminal.ansiYellow": c.base09,
                "terminal.ansiBlue": c.base0D,
                "terminal.ansiMagenta": c.base0E,
                "terminal.ansiCyan": c.base0C,
                "terminal.ansiWhite": c.base05,
                "terminal.ansiBrightBlack": c.base03,
                "terminal.ansiBrightRed": c.base08,
                "terminal.ansiBrightGreen": c.base0B,
                "terminal.ansiBrightYellow": c.base09,
                "terminal.ansiBrightBlue": c.base0D,
                "terminal.ansiBrightMagenta": c.base0E,
                "terminal.ansiBrightCyan": c.base0C,
                "terminal.ansiBrightWhite": c.base07,
                "button.background": c.base0A,
                "button.foreground": c.base00,
                "input.background": c.base00,
                "input.foreground": c.base05,
                "input.border": c.base01,
                "focusBorder": c.base0A,
            },
            tokenColors: [
                { scope: "comment", settings: { foreground: c.base03, fontStyle: "italic" } },
                { scope: ["keyword", "storage.type", "storage.modifier"], settings: { foreground: c.base0E } },
                { scope: "string", settings: { foreground: c.base0B } },
                { scope: ["constant.numeric", "constant.language"], settings: { foreground: c.base09 } },
                { scope: "variable", settings: { foreground: c.base05 } },
                { scope: "variable.parameter", settings: { foreground: c.base0C } },
                { scope: ["entity.name.function", "support.function"], settings: { foreground: c.base0D } },
                { scope: ["entity.name.type", "entity.name.class"], settings: { foreground: c.base0A } },
                { scope: "entity.name.tag", settings: { foreground: c.base08 } },
                { scope: "entity.other.attribute-name", settings: { foreground: c.base09 } },
                { scope: "punctuation", settings: { foreground: c.base04 } },
                { scope: "meta.decorator", settings: { foreground: c.base0E } },
            ],
            _prism: {
                generator: "prism-211-monochromatic",
                heroHue: this._currentPalette?.config.heroHue ?? 211,
                timestamp: new Date().toISOString(),
            },
        };
    }
    _update() {
        this._panel.webview.html = this._getHtmlForWebview();
    }
    _getHtmlForWebview() {
        const semanticColorsJSON = JSON.stringify(exports.SEMANTIC_COLORS);
        return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Prism 211° Generator</title>
  <style>
    :root {
      --bg: var(--vscode-editor-background);
      --fg: var(--vscode-editor-foreground);
      --accent: #54aeff;
      --surface: var(--vscode-sideBar-background);
      --border: var(--vscode-panel-border);
    }
    
    * { box-sizing: border-box; margin: 0; padding: 0; }
    
    body {
      font-family: var(--vscode-font-family);
      background: var(--bg);
      color: var(--fg);
      padding: 24px;
      max-width: 1200px;
      margin: 0 auto;
    }
    
    h1 {
      font-size: 2rem;
      font-weight: 300;
      margin-bottom: 8px;
    }
    
    h1 span { color: var(--accent); }
    
    .subtitle {
      opacity: 0.7;
      margin-bottom: 32px;
      line-height: 1.5;
    }
    
    .philosophy {
      background: linear-gradient(135deg, rgba(84, 174, 255, 0.1), rgba(84, 174, 255, 0.02));
      border: 1px solid rgba(84, 174, 255, 0.2);
      border-radius: 12px;
      padding: 16px 20px;
      margin-bottom: 32px;
      font-size: 0.9rem;
    }
    
    .philosophy strong { color: var(--accent); }
    
    /* Controls */
    .controls {
      display: grid;
      grid-template-columns: 1fr 1fr;
      gap: 24px;
      margin-bottom: 32px;
    }
    
    .control-group {
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 20px;
    }
    
    .control-group h3 {
      font-size: 0.9rem;
      text-transform: uppercase;
      letter-spacing: 0.1em;
      opacity: 0.6;
      margin-bottom: 16px;
    }
    
    /* Hue Selection */
    .hue-control {
      display: flex;
      flex-direction: column;
      gap: 16px;
    }
    
    .hue-display {
      display: flex;
      align-items: center;
      gap: 20px;
    }
    
    .hue-preview {
      width: 80px;
      height: 80px;
      border-radius: 12px;
      border: 2px solid rgba(255,255,255,0.1);
    }
    
    .hue-value {
      flex: 1;
    }
    
    .hue-number {
      font-size: 3rem;
      font-weight: 700;
      color: var(--accent);
      line-height: 1;
    }
    
    .hue-number::after { content: "°"; font-size: 1.5rem; }
    
    .hue-label { 
      opacity: 0.6; 
      margin-top: 4px;
      font-size: 0.85rem;
    }
    
    .slider-row {
      display: flex;
      align-items: center;
      gap: 12px;
    }
    
    .slider-row label {
      min-width: 70px;
      font-size: 0.85rem;
    }
    
    .slider-row input[type="range"] {
      flex: 1;
      height: 6px;
      -webkit-appearance: none;
      appearance: none;
      background: linear-gradient(to right, rgba(255,255,255,0.1), rgba(255,255,255,0.25));
      border: 1px solid rgba(255,255,255,0.15);
      border-radius: 3px;
      outline: none;
    }
    
    .slider-row input[type="range"]::-webkit-slider-thumb {
      -webkit-appearance: none;
      appearance: none;
      width: 20px;
      height: 20px;
      border-radius: 50%;
      background: var(--accent);
      border: 2px solid rgba(255,255,255,0.3);
      box-shadow: 0 2px 6px rgba(0,0,0,0.3);
      cursor: pointer;
    }
    
    .slider-row input[type="range"]::-moz-range-track {
      height: 6px;
      background: linear-gradient(to right, rgba(255,255,255,0.1), rgba(255,255,255,0.25));
      border: 1px solid rgba(255,255,255,0.15);
      border-radius: 3px;
    }
    
    .slider-row input[type="range"]::-moz-range-thumb {
      width: 20px;
      height: 20px;
      border-radius: 50%;
      background: var(--accent);
      border: 2px solid rgba(255,255,255,0.3);
      box-shadow: 0 2px 6px rgba(0,0,0,0.3);
      cursor: pointer;
    }
    
    .slider-row span {
      min-width: 50px;
      text-align: right;
      font-family: monospace;
    }
    
    /* Gradient Preview */
    .gradient-preview {
      height: 40px;
      border-radius: 8px;
      margin-top: 16px;
      border: 1px solid var(--border);
    }
    
    /* Options */
    .options {
      display: flex;
      flex-direction: column;
      gap: 16px;
    }
    
    .option-row {
      display: flex;
      gap: 12px;
    }
    
    .option-btn {
      flex: 1;
      padding: 12px;
      background: var(--bg);
      border: 1px solid var(--border);
      border-radius: 8px;
      color: var(--fg);
      cursor: pointer;
      transition: all 0.2s;
    }
    
    .option-btn:hover { border-color: var(--accent); }
    .option-btn.active {
      background: rgba(84, 174, 255, 0.1);
      border-color: var(--accent);
      color: var(--accent);
    }
    
    .generate-btn {
      width: 100%;
      padding: 16px;
      background: var(--accent);
      border: none;
      border-radius: 8px;
      color: #000;
      font-size: 1rem;
      font-weight: 600;
      cursor: pointer;
      margin-top: 8px;
    }
    
    .generate-btn:hover { filter: brightness(1.1); }
    
    /* Palette Display */
    .palette-section {
      margin-bottom: 32px;
    }
    
    .palette-header {
      display: flex;
      justify-content: space-between;
      align-items: center;
      margin-bottom: 16px;
    }
    
    .palette-header h2 { font-weight: 400; }
    
    .contrast-badges {
      display: flex;
      gap: 12px;
    }
    
    .badge {
      padding: 4px 12px;
      border-radius: 100px;
      font-size: 0.8rem;
    }
    
    .badge.pass { background: rgba(80, 200, 120, 0.2); color: #50c878; }
    .badge.fail { background: rgba(232, 84, 84, 0.2); color: #e85454; }
    
    /* Color Grid */
    .color-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(280px, 1fr));
      gap: 12px;
    }
    
    .color-card {
      display: flex;
      align-items: center;
      gap: 16px;
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 12px;
      transition: all 0.2s;
    }
    
    .color-card:hover {
      border-color: var(--accent);
    }
    
    .color-swatch {
      width: 48px;
      height: 48px;
      border-radius: 8px;
      border: 1px solid rgba(255,255,255,0.1);
      cursor: pointer;
      position: relative;
    }
    
    .color-swatch input[type="color"] {
      position: absolute;
      width: 100%;
      height: 100%;
      opacity: 0;
      cursor: pointer;
    }
    
    .color-info {
      flex: 1;
      min-width: 0;
    }
    
    .color-name {
      font-weight: 600;
      font-size: 0.95rem;
    }
    
    .color-name .color-desc {
      font-weight: 400;
      opacity: 0.7;
    }
    
    .color-why {
      font-size: 0.75rem;
      opacity: 0.55;
      line-height: 1.4;
      margin-top: 4px;
    }
    
    .color-hex {
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: 0.9rem;
      padding: 4px 8px;
      background: var(--bg);
      border: 1px solid var(--border);
      border-radius: 4px;
      color: var(--fg);
      width: 90px;
      text-align: center;
    }
    
    /* Section Headers */
    .section-divider {
      grid-column: 1 / -1;
      padding: 20px 0 10px;
      font-size: 0.9rem;
      font-weight: 500;
      opacity: 0.8;
      border-bottom: 1px solid var(--border);
      color: var(--accent);
    }
    
    /* Save Section */
    .save-section {
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 20px;
      margin-top: 24px;
    }
    
    .name-input-row {
      display: flex;
      align-items: center;
      gap: 16px;
      margin-bottom: 16px;
    }
    
    .name-input-row label {
      font-weight: 600;
      min-width: 100px;
    }
    
    .name-input-row input {
      flex: 1;
      padding: 12px 16px;
      background: var(--bg);
      border: 1px solid var(--border);
      border-radius: 8px;
      color: var(--fg);
      font-size: 1rem;
    }
    
    .name-input-row input:focus {
      outline: none;
      border-color: var(--accent);
    }
    
    .name-input-row input::placeholder {
      opacity: 0.5;
    }
    
    /* Action Buttons */
    .actions {
      display: flex;
      gap: 12px;
    }
    
    .action-btn {
      flex: 1;
      padding: 14px;
      border-radius: 8px;
      font-size: 0.95rem;
      cursor: pointer;
      transition: all 0.2s;
    }
    
    .action-btn.primary {
      background: var(--accent);
      border: none;
      color: #000;
      font-weight: 600;
    }
    
    .action-btn.secondary {
      background: transparent;
      border: 1px solid var(--border);
      color: var(--fg);
    }
    
    .action-btn:hover {
      filter: brightness(1.1);
    }
    
    /* Preview */
    .preview-section {
      margin-top: 32px;
    }
    
    .code-preview {
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 20px;
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: 14px;
      line-height: 1.6;
      overflow-x: auto;
    }
    
    .hidden { display: none; }
    
    /* Attribution Footer */
    .attribution {
      margin-top: 48px;
      padding: 24px 0;
      border-top: 1px solid var(--border);
      text-align: center;
      font-size: 0.85rem;
      opacity: 0.7;
    }
    
    .attribution a {
      color: var(--accent);
      text-decoration: none;
      margin: 0 4px;
    }
    
    .attribution a:hover {
      text-decoration: underline;
    }
    
    .attribution span {
      margin: 0 4px;
    }
  </style>
</head>
<body>
  <h1>Straylight <span>Prism</span> Generator</h1>
  <p class="subtitle">Generate a beautiful monochromatic palette from a single hue</p>
  
  <div class="philosophy">
    <strong>Why monochromatic?</strong> Most themes use 8+ random hues that fight for attention. 
    The 211° system uses <strong>one hue</strong> with <strong>16 shades</strong> — creating visual hierarchy 
    through <strong>lightness</strong> (depth) and <strong>chroma</strong> (intensity), not color chaos.
    <br><br>
    <strong>The result:</strong> Your code becomes readable at a glance. Backgrounds recede. 
    Text is optimized for WCAG accessibility. Accents pop without screaming. 
    Every color has semantic meaning — not decoration.
  </div>
  
  <div class="controls">
    <div class="control-group">
      <h3>Hero Hue</h3>
      <div class="hue-control">
        <div class="hue-display">
          <div class="hue-preview" id="huePreview"></div>
          <div class="hue-value">
            <div class="hue-number" id="hueNumber">211</div>
            <div class="hue-label">All colors share this hue</div>
          </div>
        </div>
        
        <div class="slider-row">
          <label>Hue</label>
          <input type="range" id="hueSlider" min="0" max="360" value="211">
          <span id="hueValue">211°</span>
        </div>
        
        <div class="slider-row">
          <label>Chroma</label>
          <input type="range" id="chromaSlider" min="0" max="100" value="100">
          <span id="chromaValue">100%</span>
        </div>
        
        <div class="gradient-preview" id="gradientPreview"></div>
      </div>
    </div>
    
    <div class="control-group">
      <h3>Options</h3>
      <div class="options">
        <div class="option-row">
          <button class="option-btn active" data-mode="dark">Dark Mode</button>
          <button class="option-btn" data-mode="light">Light Mode</button>
        </div>
        <div class="option-row">
          <button class="option-btn active" data-monitor="oled">OLED (Pure Black)</button>
          <button class="option-btn" data-monitor="lcd">LCD</button>
        </div>
        <button class="generate-btn" id="generateBtn">Generate Monochromatic Palette</button>
      </div>
    </div>
  </div>
  
  <div id="paletteSection" class="palette-section hidden">
    <div class="palette-header">
      <h2>Generated Palette</h2>
      <div class="contrast-badges" id="contrastBadges">
        <span class="badge" id="textContrast">Text: --</span>
        <span class="badge" id="commentContrast">Comment: --</span>
        <span class="badge" id="accentContrast">Accent: --</span>
      </div>
    </div>
    
    <div class="color-grid" id="colorGrid"></div>
    
    <div class="save-section">
      <div class="name-input-row">
        <label for="themeName">Theme Name</label>
        <input type="text" id="themeName" placeholder="My Theme" value="">
      </div>
      <div class="actions">
        <button class="action-btn secondary" id="exportBtn">Export JSON</button>
        <button class="action-btn primary" id="applyBtn">Save & Apply Theme</button>
      </div>
    </div>
  </div>
  
  <div id="previewSection" class="preview-section hidden">
    <h3 style="margin-bottom: 12px; font-weight: 400;">Live Preview</h3>
    <div class="code-preview" id="codePreview"></div>
  </div>
  
  <footer class="attribution">
    <span>Created by</span>
    <a href="https://github.com/b7r6" target="_blank">@b7r6</a>
    <span>·</span>
    <a href="https://github.com/j-pyxal" target="_blank">@j-pyxal</a>
    <span>·</span>
    <a href="https://straylight.software" target="_blank">@straylight-software</a>
  </footer>

  <script>
    const vscode = acquireVsCodeApi();
    const semanticColors = ${semanticColorsJSON};
    
    let currentHue = 211;
    let currentChroma = 1.0;
    let currentMode = "dark";
    let currentMonitor = "oled";
    let currentColors = {};
    
    // Elements
    const hueSlider = document.getElementById("hueSlider");
    const hueNumber = document.getElementById("hueNumber");
    const hueValue = document.getElementById("hueValue");
    const huePreview = document.getElementById("huePreview");
    const chromaSlider = document.getElementById("chromaSlider");
    const chromaValue = document.getElementById("chromaValue");
    const gradientPreview = document.getElementById("gradientPreview");
    
    // OKLCH to RGB conversion (simplified for preview)
    function oklchToRgb(L, C, H) {
      // Approximate conversion for preview
      const hRad = H * Math.PI / 180;
      const a = C * Math.cos(hRad);
      const b = C * Math.sin(hRad);
      
      const l_ = L + 0.3963377774 * a + 0.2158037573 * b;
      const m_ = L - 0.1055613458 * a - 0.0638541728 * b;
      const s_ = L - 0.0894841775 * a - 1.2914855480 * b;
      
      let l = l_ * l_ * l_;
      let m = m_ * m_ * m_;
      let s = s_ * s_ * s_;
      
      let r = 4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s;
      let g = -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s;
      let bVal = -0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s;
      
      // Gamma correction
      const toSrgb = (c) => c <= 0.0031308 ? c * 12.92 : 1.055 * Math.pow(Math.max(0, c), 1/2.4) - 0.055;
      
      r = Math.max(0, Math.min(1, toSrgb(r)));
      g = Math.max(0, Math.min(1, toSrgb(g)));
      bVal = Math.max(0, Math.min(1, toSrgb(bVal)));
      
      return \`rgb(\${Math.round(r*255)}, \${Math.round(g*255)}, \${Math.round(bVal*255)})\`;
    }
    
    function updateHuePreview() {
      const color = oklchToRgb(0.7, 0.15 * currentChroma, currentHue);
      huePreview.style.background = color;
      hueNumber.textContent = Math.round(currentHue);
      hueValue.textContent = Math.round(currentHue) + "°";
      
      // Update accent color variable
      document.documentElement.style.setProperty('--accent', color);
      
      // Update gradient preview - show the monochromatic range
      const stops = [];
      for (let L = 0.1; L <= 0.9; L += 0.1) {
        stops.push(oklchToRgb(L, 0.15 * currentChroma, currentHue));
      }
      gradientPreview.style.background = \`linear-gradient(to right, \${stops.join(', ')})\`;
    }
    
    hueSlider.addEventListener("input", (e) => {
      currentHue = parseFloat(e.target.value);
      updateHuePreview();
    });
    
    chromaSlider.addEventListener("input", (e) => {
      currentChroma = parseFloat(e.target.value) / 100;
      chromaValue.textContent = e.target.value + "%";
      updateHuePreview();
    });
    
    updateHuePreview();
    
    // Mode/Monitor buttons
    document.querySelectorAll("[data-mode]").forEach(btn => {
      btn.addEventListener("click", () => {
        document.querySelectorAll("[data-mode]").forEach(b => b.classList.remove("active"));
        btn.classList.add("active");
        currentMode = btn.dataset.mode;
      });
    });
    
    document.querySelectorAll("[data-monitor]").forEach(btn => {
      btn.addEventListener("click", () => {
        document.querySelectorAll("[data-monitor]").forEach(b => b.classList.remove("active"));
        btn.classList.add("active");
        currentMonitor = btn.dataset.monitor;
      });
    });
    
    // Generate
    document.getElementById("generateBtn").addEventListener("click", () => {
      vscode.postMessage({
        command: "generate",
        config: {
          heroHue: currentHue,
          heroChroma: currentChroma,
          mode: currentMode,
          monitor: currentMonitor,
          name: Math.round(currentHue) + "° Mono"
        }
      });
    });
    
    // Render palette
    function renderPalette(palette) {
      currentColors = { ...palette.colors };
      
      const grid = document.getElementById("colorGrid");
      grid.innerHTML = "";
      
      // Group by role
      const groups = { background: [], foreground: [], accent: [] };
      semanticColors.forEach(sc => groups[sc.role].push(sc));
      
      const labels = { 
        background: "Backgrounds — Depth through lightness, not color noise", 
        foreground: "Foregrounds — Optimized for readability (WCAG AA)", 
        accent: "Accents — Your hero hue at varying intensities" 
      };
      
      for (const role of ["background", "foreground", "accent"]) {
        const divider = document.createElement("div");
        divider.className = "section-divider";
        divider.textContent = labels[role];
        grid.appendChild(divider);
        
        groups[role].forEach(sc => {
          const hex = palette.colors[sc.id];
          const card = document.createElement("div");
          card.className = "color-card";
          card.innerHTML = \`
            <div class="color-swatch" style="background: \${hex}">
              <input type="color" value="\${hex}" data-id="\${sc.id}">
            </div>
            <div class="color-info">
              <div class="color-name">\${sc.name} <span class="color-desc">— \${sc.description}</span></div>
              <div class="color-why">\${sc.why}</div>
            </div>
            <input type="text" class="color-hex" value="\${hex}" data-id="\${sc.id}">
          \`;
          grid.appendChild(card);
          
          // Color picker change
          card.querySelector('input[type="color"]').addEventListener("input", (e) => {
            const newHex = e.target.value;
            currentColors[sc.id] = newHex;
            card.querySelector(".color-swatch").style.background = newHex;
            card.querySelector(".color-hex").value = newHex;
            vscode.postMessage({ command: "updateColor", colorId: sc.id, hex: newHex });
            updatePreview();
          });
          
          // Hex input change
          card.querySelector(".color-hex").addEventListener("change", (e) => {
            let newHex = e.target.value;
            if (!newHex.startsWith("#")) newHex = "#" + newHex;
            if (/^#[0-9a-fA-F]{6}$/.test(newHex)) {
              currentColors[sc.id] = newHex;
              card.querySelector(".color-swatch").style.background = newHex;
              card.querySelector('input[type="color"]').value = newHex;
              vscode.postMessage({ command: "updateColor", colorId: sc.id, hex: newHex });
              updatePreview();
            }
          });
        });
      }
      
      document.getElementById("paletteSection").classList.remove("hidden");
      document.getElementById("previewSection").classList.remove("hidden");
      
      // Set default theme name
      const nameInput = document.getElementById("themeName");
      if (!nameInput.value) {
        nameInput.value = Math.round(currentHue) + "° Monochrome";
      }
      
      updateContrastBadges(palette.contrast);
      updatePreview();
    }
    
    function updateContrastBadges(contrast) {
      const textBadge = document.getElementById("textContrast");
      const commentBadge = document.getElementById("commentContrast");
      const accentBadge = document.getElementById("accentContrast");
      
      textBadge.textContent = "Text: " + contrast.text + ":1";
      textBadge.className = "badge " + (contrast.text >= 4.5 ? "pass" : "fail");
      
      commentBadge.textContent = "Comment: " + contrast.comment + ":1";
      commentBadge.className = "badge " + (contrast.comment >= 3.0 ? "pass" : "fail");
      
      accentBadge.textContent = "Accent: " + contrast.accent + ":1";
      accentBadge.className = "badge " + (contrast.accent >= 3.0 ? "pass" : "fail");
    }
    
    function updatePreview() {
      const c = currentColors;
      const preview = document.getElementById("codePreview");
      preview.style.background = c.base00;
      preview.innerHTML = \`
        <span style="color:\${c.base03}">// Monochromatic theme at \${Math.round(currentHue)}°</span><br>
        <span style="color:\${c.base0E}">interface</span> <span style="color:\${c.base0A}">Theme</span> {<br>
        &nbsp;&nbsp;<span style="color:\${c.base05}">name</span>: <span style="color:\${c.base0B}">"perfect-blue"</span>;<br>
        &nbsp;&nbsp;<span style="color:\${c.base05}">hue</span>: <span style="color:\${c.base09}">\${Math.round(currentHue)}</span>;<br>
        &nbsp;&nbsp;<span style="color:\${c.base05}">monochromatic</span>: <span style="color:\${c.base09}">true</span>;<br>
        }<br><br>
        <span style="color:\${c.base0E}">const</span> <span style="color:\${c.base05}">palette</span> = <span style="color:\${c.base0D}">generate</span>(<span style="color:\${c.base0C}">config</span>);<br>
        <span style="color:\${c.base0E}">export</span> { <span style="color:\${c.base05}">palette</span> };
      \`;
    }
    
    // Get theme name from input
    function getThemeName() {
      const nameInput = document.getElementById("themeName");
      return nameInput.value.trim() || Math.round(currentHue) + "° Monochrome";
    }
    
    // Export
    document.getElementById("exportBtn").addEventListener("click", () => {
      const name = getThemeName();
      vscode.postMessage({ command: "export", name, colors: currentColors });
    });
    
    // Apply
    document.getElementById("applyBtn").addEventListener("click", () => {
      const name = getThemeName();
      vscode.postMessage({ command: "apply", name, colors: currentColors });
    });
    
    // Message handler
    window.addEventListener("message", (event) => {
      const message = event.data;
      switch (message.command) {
        case "paletteGenerated":
          renderPalette(message.palette);
          break;
        case "contrastUpdated":
          updateContrastBadges(message.contrast);
          break;
      }
    });
  </script>
</body>
</html>`;
    }
    dispose() {
        Prism211GeneratorPanel.currentPanel = undefined;
        this._panel.dispose();
        while (this._disposables.length) {
            const x = this._disposables.pop();
            if (x)
                x.dispose();
        }
    }
}
exports.Prism211GeneratorPanel = Prism211GeneratorPanel;
Prism211GeneratorPanel.viewType = "prism211Generator";
//# sourceMappingURL=prism211Generator.js.map