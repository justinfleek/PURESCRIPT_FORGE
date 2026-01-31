import * as vscode from "vscode";
import * as path from "path";
import { ThemePreviewPanel } from "./themePreviewPanel";
import { ThemeConfig, MonitorType, ThemeVariant } from "./types";
import { generateVariants, generateVSCodeTheme } from "./prismColor";

export class ThemeGeneratorPanel {
  public static currentPanel: ThemeGeneratorPanel | undefined;
  public static readonly viewType = "prismThemeGenerator";

  private readonly _panel: vscode.WebviewPanel;
  private readonly _extensionUri: vscode.Uri;
  private _disposables: vscode.Disposable[] = [];

  public static createOrShow(extensionUri: vscode.Uri) {
    const column = vscode.window.activeTextEditor
      ? vscode.window.activeTextEditor.viewColumn
      : undefined;

    // If we already have a panel, show it
    if (ThemeGeneratorPanel.currentPanel) {
      ThemeGeneratorPanel.currentPanel._panel.reveal(column);
      return;
    }

    // Otherwise, create a new panel
    const viewColumn = column !== undefined ? column : vscode.ViewColumn.One;
    const panel = vscode.window.createWebviewPanel(
      ThemeGeneratorPanel.viewType,
      "Prism Theme Generator",
      viewColumn,
      {
        enableScripts: true,
        localResourceRoots: [
          vscode.Uri.joinPath(extensionUri, "media"),
          vscode.Uri.joinPath(extensionUri, "out")
        ]
      }
    );

    ThemeGeneratorPanel.currentPanel = new ThemeGeneratorPanel(
      panel,
      extensionUri
    );
  }

  private constructor(panel: vscode.WebviewPanel, extensionUri: vscode.Uri) {
    this._panel = panel;
    this._extensionUri = extensionUri;

    // Set the webview's initial html content
    this._update();

    // Listen for when the panel is disposed
    // This happens when the user closes the panel or when the panel is closed programmatically
    this._panel.onDidDispose(() => this.dispose(), null, this._disposables);

    // Handle messages from the webview
    this._panel.webview.onDidReceiveMessage(
      (message) => {
        switch (message.command) {
          case "generateTheme":
            this._generateTheme(message.config);
            return;
          case "previewTheme":
            this._previewTheme(message.config);
            return;
          case "previewVariant":
            this._previewVariant(message.variant);
            return;
        }
      },
      null,
      this._disposables
    );
  }

  private _update() {
    const webview = this._panel.webview;
    this._panel.webview.html = this._getHtmlForWebview(webview);
  }

  private _getHtmlForWebview(webview: vscode.Webview): string {
    const scriptUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "out", "themeGenerator.js")
    );
    const styleUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "out", "themeGenerator.css")
    );

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <link href="${styleUri}" rel="stylesheet">
  <title>Prism Theme Generator</title>
</head>
<body>
  <div class="container">
    <h1>Prism Theme Generator</h1>
    
    <div class="section">
      <h2>Base Color</h2>
      <div id="baseColorWheel" class="color-wheel-container"></div>
      <div class="color-info">
        <label>HSL: <span id="baseHSL">211°, 100%, 50%</span></label>
        <label>Hex: <span id="baseHex">#54aeff</span></label>
      </div>
    </div>

    <div class="section">
      <h2>Hero Color</h2>
      <div id="heroColorWheel" class="color-wheel-container"></div>
      <div class="color-info">
        <label>HSL: <span id="heroHSL">211°, 100%, 66%</span></label>
        <label>Hex: <span id="heroHex">#54aeff</span></label>
      </div>
    </div>

    <div class="section">
      <h2>Monitor Settings</h2>
      <div class="monitor-controls">
        <label>
          <input type="radio" name="monitorType" value="OLED" checked>
          OLED
        </label>
        <label>
          <input type="radio" name="monitorType" value="LCD">
          LCD
        </label>
      </div>
      <div class="slider-container">
        <label>Black Balance: <span id="blackBalanceValue">11%</span></label>
        <input type="range" id="blackBalanceSlider" min="0" max="20" value="11" step="0.1">
      </div>
    </div>

    <div class="section">
      <h2>Theme Mode</h2>
      <div class="mode-controls">
        <label>
          <input type="radio" name="themeMode" value="dark" checked>
          Dark Mode
        </label>
        <label>
          <input type="radio" name="themeMode" value="light">
          Light Mode
        </label>
      </div>
    </div>

    <div class="section">
      <button id="generateBtn" class="generate-btn">Generate Themes</button>
      <button id="previewBtn" class="preview-btn">Preview</button>
    </div>

    <div id="themeList" class="theme-list"></div>
  </div>

  <script src="${scriptUri}"></script>
</body>
</html>`;
  }

  private async _generateTheme(config: ThemeConfig) {
    try {
      // Use the verified OKLCH generator (TypeScript port of Haskell/Lean4)
      const variants = generateVariants(config);
      
      // Log verification status
      variants.forEach(v => {
        console.log(`[PRISM] ${v.name}: text=${v.contrast.text}:1, comment=${v.contrast.comment}:1, accent=${v.contrast.accent}:1 ${v.contrast.wcagVerified ? '✓ WCAG' : '⚠'}`);
      });
      
      this._panel.webview.postMessage({
        command: "themesGenerated",
        variants: variants
      });
    } catch (error) {
      vscode.window.showErrorMessage(`Failed to generate themes: ${error}`);
      this._panel.webview.postMessage({
        command: "themeGenerationError",
        error: String(error)
      });
    }
  }

  private _previewTheme(config: ThemeConfig) {
    // Generate verified variant for preview
    const variants = generateVariants(config);
    const variant = variants.find(v => v.name === 'Tuned') || variants[0];
    ThemePreviewPanel.createOrShow(this._extensionUri, variant);
  }

  private _previewVariant(variant: ThemeVariant) {
    ThemePreviewPanel.createOrShow(this._extensionUri, variant);
  }

  public dispose() {
    ThemeGeneratorPanel.currentPanel = undefined;

    // Clean up our resources
    this._panel.dispose();

    while (this._disposables.length) {
      const x = this._disposables.pop();
      if (x) {
        x.dispose();
      }
    }
  }
}
