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
exports.ThemePreviewPanel = void 0;
const vscode = __importStar(require("vscode"));
const typeGuards_1 = require("./typeGuards");
class ThemePreviewPanel {
    static createOrShow(extensionUri, variant) {
        const column = vscode.window.activeTextEditor
            ? vscode.window.activeTextEditor.viewColumn
            : undefined;
        if (ThemePreviewPanel.currentPanel) {
            ThemePreviewPanel.currentPanel._panel.reveal(column);
            if (variant) {
                ThemePreviewPanel.currentPanel._update(variant);
            }
            return;
        }
        const viewColumn = column !== undefined ? column : vscode.ViewColumn.Two;
        const panel = vscode.window.createWebviewPanel(ThemePreviewPanel.viewType, "Theme Preview", viewColumn, {
            enableScripts: true,
            localResourceRoots: [
                vscode.Uri.joinPath(extensionUri, "media"),
                vscode.Uri.joinPath(extensionUri, "out")
            ]
        });
        ThemePreviewPanel.currentPanel = new ThemePreviewPanel(panel, extensionUri);
        if (variant) {
            ThemePreviewPanel.currentPanel._update(variant);
        }
    }
    constructor(panel, extensionUri) {
        this._disposables = [];
        this._panel = panel;
        this._extensionUri = extensionUri;
        this._panel.onDidDispose(() => this.dispose(), null, this._disposables);
    }
    _update(variant) {
        const webview = this._panel.webview;
        this._panel.webview.html = this._getHtmlForWebview(webview, variant);
    }
    _getHtmlForWebview(webview, variant) {
        const colors = variant.colors;
        const bgColor = (0, typeGuards_1.getColorOrDefault)(colors, "base00", "#000000");
        const fgColor = (0, typeGuards_1.getColorOrDefault)(colors, "base05", "#ffffff");
        return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Theme Preview: ${variant.name}</title>
  <style>
    * { margin: 0; padding: 0; box-sizing: border-box; }
    body {
      background: ${bgColor};
      color: ${fgColor};
      padding: 20px;
      font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
      min-height: 100vh;
    }
    .header {
      margin-bottom: 30px;
      padding-bottom: 20px;
      border-bottom: 2px solid ${(0, typeGuards_1.getColorOrDefault)(colors, "base02", bgColor)};
    }
    h1 {
      font-size: 24px;
      margin-bottom: 10px;
      color: ${(0, typeGuards_1.getColorOrDefault)(colors, "base0A", fgColor)};
    }
    .variant-info {
      color: ${(0, typeGuards_1.getColorOrDefault)(colors, "base04", fgColor)};
      font-size: 14px;
    }
    .color-grid {
      display: grid;
      grid-template-columns: repeat(4, 1fr);
      gap: 10px;
      margin-bottom: 30px;
    }
    .color-swatch {
      aspect-ratio: 1;
      border-radius: 4px;
      border: 1px solid ${(0, typeGuards_1.getColorOrDefault)(colors, "base02", bgColor)};
      position: relative;
      cursor: pointer;
    }
    .color-swatch:hover::after {
      content: attr(data-hex);
      position: absolute;
      bottom: -20px;
      left: 50%;
      transform: translateX(-50%);
      background: ${(0, typeGuards_1.getColorOrDefault)(colors, "base01", bgColor)};
      padding: 2px 6px;
      border-radius: 2px;
      font-size: 11px;
      white-space: nowrap;
    }
    .color-label {
      position: absolute;
      top: 4px;
      left: 4px;
      font-size: 10px;
      font-weight: bold;
      color: ${fgColor};
      text-shadow: 0 0 2px ${bgColor};
    }
    .preview-section {
      margin-top: 30px;
      padding: 20px;
      background: ${(0, typeGuards_1.getColorOrDefault)(colors, "base01", bgColor)};
      border-radius: 4px;
    }
    .preview-section h2 {
      color: ${(0, typeGuards_1.getColorOrDefault)(colors, "base0A", fgColor)};
      margin-bottom: 15px;
    }
    .code-block {
      background: ${bgColor};
      padding: 15px;
      border-radius: 4px;
      border-left: 3px solid ${(0, typeGuards_1.getColorOrDefault)(colors, "base0A", fgColor)};
      font-family: 'Consolas', 'Monaco', monospace;
      font-size: 13px;
      overflow-x: auto;
    }
    .keyword { color: ${(0, typeGuards_1.getColorOrDefault)(colors, "base0E", fgColor)}; }
    .string { color: ${(0, typeGuards_1.getColorOrDefault)(colors, "base0B", fgColor)}; }
    .function { color: ${(0, typeGuards_1.getColorOrDefault)(colors, "base0D", fgColor)}; }
    .comment { color: ${(0, typeGuards_1.getColorOrDefault)(colors, "base03", fgColor)}; font-style: italic; }
  </style>
</head>
<body>
  <div class="header">
    <h1>${variant.name}</h1>
    <div class="variant-info">
      Background Lightness: ${(variant.backgroundLightness * 100).toFixed(1)}%
    </div>
  </div>

  <div class="color-grid">
    <div class="color-swatch" style="background: ${colors.base00}" data-hex="${colors.base00}">
      <span class="color-label">00</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base01}" data-hex="${colors.base01}">
      <span class="color-label">01</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base02}" data-hex="${colors.base02}">
      <span class="color-label">02</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base03}" data-hex="${colors.base03}">
      <span class="color-label">03</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base04}" data-hex="${colors.base04}">
      <span class="color-label">04</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base05}" data-hex="${colors.base05}">
      <span class="color-label">05</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base06}" data-hex="${colors.base06}">
      <span class="color-label">06</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base07}" data-hex="${colors.base07}">
      <span class="color-label">07</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base08}" data-hex="${colors.base08}">
      <span class="color-label">08</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base09}" data-hex="${colors.base09}">
      <span class="color-label">09</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base0A}" data-hex="${colors.base0A}">
      <span class="color-label">0A</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base0B}" data-hex="${colors.base0B}">
      <span class="color-label">0B</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base0C}" data-hex="${colors.base0C}">
      <span class="color-label">0C</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base0D}" data-hex="${colors.base0D}">
      <span class="color-label">0D</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base0E}" data-hex="${colors.base0E}">
      <span class="color-label">0E</span>
    </div>
    <div class="color-swatch" style="background: ${colors.base0F}" data-hex="${colors.base0F}">
      <span class="color-label">0F</span>
    </div>
  </div>

  <div class="preview-section">
    <h2>Code Preview</h2>
    <div class="code-block">
<span class="keyword">function</span> <span class="function">example</span>() {<br/>
&nbsp;&nbsp;<span class="comment">// This is a comment</span><br/>
&nbsp;&nbsp;<span class="keyword">const</span> message = <span class="string">"Hello, World!"</span>;<br/>
&nbsp;&nbsp;<span class="keyword">return</span> message;<br/>
}
    </div>
  </div>
</body>
</html>`;
    }
    dispose() {
        ThemePreviewPanel.currentPanel = undefined;
        this._panel.dispose();
        while (this._disposables.length) {
            const x = this._disposables.pop();
            if (x) {
                x.dispose();
            }
        }
    }
}
exports.ThemePreviewPanel = ThemePreviewPanel;
ThemePreviewPanel.viewType = "prismThemePreview";
//# sourceMappingURL=themePreviewPanel.js.map