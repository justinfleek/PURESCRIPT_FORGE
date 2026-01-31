import * as vscode from "vscode";
import { ThemeConfig, ThemeVariant } from "./types";
import { 
  ThemePreset, 
  ALL_PRESETS, 
  LUXURY_PRESETS,
  GLASS_PRESETS,
  BENTO_PRESETS,
  NEUMORPHISM_PRESETS,
  RESPONSIVE_PRESETS,
  EASTER_EGG_PRESETS,
  presetToConfig,
  presetToVariant
} from "./presetGallery";
import { installTheme, base16ToVSCodeTheme } from "./themeInstaller";

export class ThemeGeneratorPanelV2 {
  public static currentPanel: ThemeGeneratorPanelV2 | undefined;
  public static readonly viewType = "prismThemeGeneratorV2";

  private readonly _panel: vscode.WebviewPanel;
  private readonly _extensionUri: vscode.Uri;
  private readonly _context: vscode.ExtensionContext;
  private _disposables: vscode.Disposable[] = [];

  public static createOrShow(context: vscode.ExtensionContext) {
    const column = vscode.window.activeTextEditor?.viewColumn ?? vscode.ViewColumn.One;

    if (ThemeGeneratorPanelV2.currentPanel) {
      ThemeGeneratorPanelV2.currentPanel._panel.reveal(column);
      return;
    }

    const panel = vscode.window.createWebviewPanel(
      ThemeGeneratorPanelV2.viewType,
      "Prism Premium Themes",
      column,
      {
        enableScripts: true,
        retainContextWhenHidden: true,
        localResourceRoots: [
          vscode.Uri.joinPath(context.extensionUri, "media"),
          vscode.Uri.joinPath(context.extensionUri, "out")
        ]
      }
    );

    ThemeGeneratorPanelV2.currentPanel = new ThemeGeneratorPanelV2(panel, context);
  }

  private constructor(panel: vscode.WebviewPanel, context: vscode.ExtensionContext) {
    this._panel = panel;
    this._context = context;
    this._extensionUri = context.extensionUri;

    this._update();

    this._panel.onDidDispose(() => this.dispose(), null, this._disposables);

    this._panel.webview.onDidReceiveMessage(
      async (message) => {
        switch (message.command) {
          case "applyPreset":
            await this._applyPreset(message.presetId);
            break;
          case "previewPreset":
            this._previewPreset(message.presetId);
            break;
          case "generateCustom":
            await this._generateCustomTheme(message.config);
            break;
          case "setEffectsEnabled":
            // Store preference
            await this._context.globalState.update("prism.effectsEnabled", message.enabled);
            break;
        }
      },
      null,
      this._disposables
    );
  }

  private async _applyPreset(presetId: string) {
    const preset = ALL_PRESETS.find(p => p.id === presetId);
    if (!preset) {
      vscode.window.showErrorMessage(`Preset "${presetId}" not found`);
      return;
    }

    try {
      await installTheme(this._context, preset);
    } catch (error) {
      vscode.window.showErrorMessage(`Failed to install theme: ${error}`);
    }
  }

  private _previewPreset(presetId: string) {
    const preset = ALL_PRESETS.find(p => p.id === presetId);
    if (!preset) return;

    // Send preview colors back to webview
    this._panel.webview.postMessage({
      command: "previewColors",
      colors: preset.palette,
      effects: preset.effects
    });
  }

  private async _generateCustomTheme(config: ThemeConfig) {
    // Try to call Haskell backend, fallback to preset-based generation
    try {
      const { generateThemeVariants } = await import("./ffiBridge");
      const variants = await generateThemeVariants(config);
      this._panel.webview.postMessage({
        command: "customThemeGenerated",
        variants
      });
    } catch {
      // Fallback: find closest preset and adjust
      vscode.window.showWarningMessage(
        "Backend not available. Using preset-based generation."
      );
    }
  }

  private _update() {
    this._panel.webview.html = this._getHtmlForWebview();
  }

  private _getHtmlForWebview(): string {
    const effectsEnabled = this._context.globalState.get("prism.effectsEnabled", true);
    
    // Generate preset cards HTML
    const generatePresetCards = (presets: ThemePreset[], category: string) => {
      return presets.map(p => `
        <div class="preset-card" data-id="${p.id}" data-category="${category}">
          <div class="preset-preview" style="
            background: ${p.palette.base00};
            ${p.effects?.glow ? `box-shadow: inset 0 0 60px ${p.effects.glowColor}20;` : ''}
          ">
            <div class="code-sample">
              <span class="comment" style="color:${p.palette.base03}">// ${p.name}</span>
              <span class="keyword" style="color:${p.palette.base0E}">const</span>
              <span class="variable" style="color:${p.palette.base05}">theme</span>
              <span class="operator" style="color:${p.palette.base05}">=</span>
              <span class="string" style="color:${p.palette.base0B}">"${p.id}"</span>
              <span class="punctuation" style="color:${p.palette.base05}">;</span>
              <br>
              <span class="type" style="color:${p.palette.base0A}">Type</span>
              <span class="function" style="color:${p.palette.base0D}">.apply</span>
              <span class="punctuation" style="color:${p.palette.base05}">()</span>
            </div>
            ${p.effects?.glow ? `<div class="glow-effect" style="background:${p.effects.glowColor}"></div>` : ''}
          </div>
          <div class="preset-info">
            <h3 class="preset-name">${p.name}</h3>
            <p class="preset-desc">${p.inspiration}</p>
            <div class="preset-tags">
              ${p.tags.slice(0, 3).map(t => `<span class="tag">${t}</span>`).join('')}
            </div>
            <div class="preset-actions">
              <button class="btn-preview" data-id="${p.id}">Preview</button>
              <button class="btn-apply" data-id="${p.id}">Apply</button>
            </div>
          </div>
        </div>
      `).join('');
    };

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Prism Premium Themes</title>
  <style>
    :root {
      --bg: var(--vscode-editor-background);
      --fg: var(--vscode-editor-foreground);
      --accent: var(--vscode-focusBorder);
      --surface: var(--vscode-sideBar-background);
      --border: var(--vscode-panel-border);
      --gold: #d4af37;
      --gold-subtle: rgba(212, 175, 55, 0.1);
    }
    
    * {
      box-sizing: border-box;
      margin: 0;
      padding: 0;
    }
    
    body {
      font-family: var(--vscode-font-family);
      background: var(--bg);
      color: var(--fg);
      padding: 20px;
      overflow-x: hidden;
    }
    
    /* Hero */
    .hero {
      text-align: center;
      padding: 40px 20px;
      margin-bottom: 30px;
    }
    
    .hero h1 {
      font-size: 2.5rem;
      font-weight: 300;
      margin-bottom: 10px;
    }
    
    .hero h1 span {
      background: linear-gradient(135deg, var(--gold) 0%, #f7e7ce 50%, var(--gold) 100%);
      -webkit-background-clip: text;
      -webkit-text-fill-color: transparent;
    }
    
    .hero p {
      opacity: 0.7;
      max-width: 500px;
      margin: 0 auto;
    }
    
    /* Tabs */
    .tabs {
      display: flex;
      gap: 8px;
      margin-bottom: 30px;
      flex-wrap: wrap;
      justify-content: center;
    }
    
    .tab {
      padding: 10px 20px;
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: 8px;
      cursor: pointer;
      transition: all 0.2s;
      font-size: 0.9rem;
    }
    
    .tab:hover {
      border-color: var(--gold);
    }
    
    .tab.active {
      background: var(--gold-subtle);
      border-color: var(--gold);
      color: var(--gold);
    }
    
    /* Grid */
    .preset-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(320px, 1fr));
      gap: 20px;
    }
    
    .preset-card {
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: 16px;
      overflow: hidden;
      transition: transform 0.3s, box-shadow 0.3s;
    }
    
    .preset-card:hover {
      transform: translateY(-4px);
      box-shadow: 0 12px 40px rgba(0,0,0,0.3);
    }
    
    .preset-card[data-category]:not([data-visible="true"]) {
      display: none;
    }
    
    .preset-preview {
      height: 140px;
      padding: 16px;
      position: relative;
      overflow: hidden;
      font-family: var(--vscode-editor-font-family, 'Consolas', monospace);
      font-size: 12px;
    }
    
    .code-sample {
      position: relative;
      z-index: 1;
      line-height: 1.8;
    }
    
    .glow-effect {
      position: absolute;
      width: 150px;
      height: 150px;
      border-radius: 50%;
      right: -30px;
      bottom: -30px;
      filter: blur(50px);
      opacity: 0.4;
    }
    
    .preset-info {
      padding: 16px;
    }
    
    .preset-name {
      font-size: 1.1rem;
      font-weight: 500;
      margin-bottom: 4px;
    }
    
    .preset-desc {
      font-size: 0.85rem;
      opacity: 0.6;
      font-style: italic;
      margin-bottom: 12px;
    }
    
    .preset-tags {
      display: flex;
      gap: 6px;
      margin-bottom: 12px;
      flex-wrap: wrap;
    }
    
    .tag {
      font-size: 0.7rem;
      padding: 3px 8px;
      background: var(--gold-subtle);
      border-radius: 100px;
      color: var(--gold);
    }
    
    .preset-actions {
      display: flex;
      gap: 8px;
    }
    
    .preset-actions button {
      flex: 1;
      padding: 8px 16px;
      border: none;
      border-radius: 6px;
      cursor: pointer;
      font-size: 0.85rem;
      transition: all 0.2s;
    }
    
    .btn-preview {
      background: var(--surface);
      border: 1px solid var(--border) !important;
      color: var(--fg);
    }
    
    .btn-preview:hover {
      border-color: var(--gold) !important;
    }
    
    .btn-apply {
      background: var(--gold);
      color: #000;
    }
    
    .btn-apply:hover {
      filter: brightness(1.1);
    }
    
    /* Effects toggle */
    .effects-toggle {
      position: fixed;
      bottom: 20px;
      right: 20px;
      display: flex;
      align-items: center;
      gap: 10px;
      padding: 10px 16px;
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: 100px;
      font-size: 0.85rem;
    }
    
    .effects-toggle input {
      width: 16px;
      height: 16px;
    }
    
    /* Cursor spotlight effect */
    #cursor-spotlight {
      position: fixed;
      width: 300px;
      height: 300px;
      border-radius: 50%;
      background: radial-gradient(circle, var(--gold-subtle) 0%, transparent 70%);
      pointer-events: none;
      transform: translate(-50%, -50%);
      opacity: 0;
      transition: opacity 0.3s;
      z-index: 9999;
    }
    
    body.effects-on #cursor-spotlight {
      opacity: 1;
    }
    
    /* Section headers */
    .section-header {
      text-align: center;
      margin: 40px 0 20px;
      padding-bottom: 10px;
      border-bottom: 1px solid var(--border);
    }
    
    .section-header h2 {
      font-weight: 400;
      font-size: 1.3rem;
    }
    
    .section-header p {
      opacity: 0.6;
      font-size: 0.9rem;
    }
  </style>
</head>
<body class="${effectsEnabled ? 'effects-on' : ''}">
  <div id="cursor-spotlight"></div>
  
  <div class="hero">
    <h1>Prism <span>Premium</span></h1>
    <p>Luxury themes with perceptually uniform color science and subtle micro-interactions</p>
  </div>
  
  <div class="tabs">
    <button class="tab active" data-category="all">All Themes</button>
    <button class="tab" data-category="luxury">🏛️ Luxury</button>
    <button class="tab" data-category="glass">💎 Glass</button>
    <button class="tab" data-category="bento">📦 Bento</button>
    <button class="tab" data-category="neumorphism">🫧 Neumorphism</button>
    <button class="tab" data-category="responsive">✨ Responsive</button>
    <button class="tab" data-category="easter_eggs">🎮 Easter Eggs</button>
  </div>
  
  <div class="section-header" id="luxury-section">
    <h2>🏛️ Luxury Marble Collection</h2>
    <p>Black marble with gold veining, obsidian with rose gold, sapphire depths</p>
  </div>
  <div class="preset-grid" data-section="luxury">
    ${generatePresetCards(LUXURY_PRESETS, 'luxury')}
  </div>
  
  <div class="section-header" id="glass-section">
    <h2>💎 Glassmorphism</h2>
    <p>Frosted glass with depth, blur, and luminous borders</p>
  </div>
  <div class="preset-grid" data-section="glass">
    ${generatePresetCards(GLASS_PRESETS, 'glass')}
  </div>
  
  <div class="section-header" id="bento-section">
    <h2>📦 Floating Bento</h2>
    <p>Organized compartments with depth and subtle hover lift</p>
  </div>
  <div class="preset-grid" data-section="bento">
    ${generatePresetCards(BENTO_PRESETS, 'bento')}
  </div>
  
  <div class="section-header" id="neumorphism-section">
    <h2>🫧 Neumorphism</h2>
    <p>Soft shadows creating tactile depth</p>
  </div>
  <div class="preset-grid" data-section="neumorphism">
    ${generatePresetCards(NEUMORPHISM_PRESETS, 'neumorphism')}
  </div>
  
  <div class="section-header" id="responsive-section">
    <h2>✨ Responsive Effects</h2>
    <p>Themes that respond to your presence</p>
  </div>
  <div class="preset-grid" data-section="responsive">
    ${generatePresetCards(RESPONSIVE_PRESETS, 'responsive')}
  </div>
  
  <div class="section-header" id="easter-section">
    <h2>🎮 Hidden Delights</h2>
    <p>Easter eggs and idle rewards</p>
  </div>
  <div class="preset-grid" data-section="easter_eggs">
    ${generatePresetCards(EASTER_EGG_PRESETS, 'easter_eggs')}
  </div>
  
  <label class="effects-toggle">
    <input type="checkbox" id="effectsToggle" ${effectsEnabled ? 'checked' : ''}>
    <span>✨ Micro-interactions</span>
  </label>

  <script>
    const vscode = acquireVsCodeApi();
    
    // Tab switching
    document.querySelectorAll('.tab').forEach(tab => {
      tab.addEventListener('click', () => {
        document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
        tab.classList.add('active');
        
        const category = tab.dataset.category;
        
        // Show/hide sections based on category
        document.querySelectorAll('.section-header').forEach(h => {
          h.style.display = category === 'all' ? 'block' : 'none';
        });
        document.querySelectorAll('.preset-grid').forEach(g => {
          const section = g.dataset.section;
          g.style.display = (category === 'all' || category === section) ? 'grid' : 'none';
        });
        
        if (category !== 'all') {
          const sectionHeader = document.getElementById(category + '-section');
          if (sectionHeader) sectionHeader.style.display = 'block';
        }
      });
    });
    
    // Preview buttons
    document.querySelectorAll('.btn-preview').forEach(btn => {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        vscode.postMessage({ command: 'previewPreset', presetId: btn.dataset.id });
      });
    });
    
    // Apply buttons
    document.querySelectorAll('.btn-apply').forEach(btn => {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        vscode.postMessage({ command: 'applyPreset', presetId: btn.dataset.id });
      });
    });
    
    // Effects toggle
    document.getElementById('effectsToggle').addEventListener('change', (e) => {
      document.body.classList.toggle('effects-on', e.target.checked);
      vscode.postMessage({ command: 'setEffectsEnabled', enabled: e.target.checked });
    });
    
    // Cursor spotlight
    const spotlight = document.getElementById('cursor-spotlight');
    let spotlightX = 0, spotlightY = 0;
    let currentX = 0, currentY = 0;
    
    document.addEventListener('mousemove', (e) => {
      spotlightX = e.clientX;
      spotlightY = e.clientY;
    });
    
    function animateSpotlight() {
      currentX += (spotlightX - currentX) * 0.1;
      currentY += (spotlightY - currentY) * 0.1;
      spotlight.style.left = currentX + 'px';
      spotlight.style.top = currentY + 'px';
      requestAnimationFrame(animateSpotlight);
    }
    animateSpotlight();
    
    // Message handler
    window.addEventListener('message', (event) => {
      const message = event.data;
      switch (message.command) {
        case 'previewColors':
          // Could show a live preview overlay
          console.log('Preview colors:', message.colors);
          break;
      }
    });
  </script>
</body>
</html>`;
  }

  public dispose() {
    ThemeGeneratorPanelV2.currentPanel = undefined;
    this._panel.dispose();
    while (this._disposables.length) {
      const x = this._disposables.pop();
      if (x) x.dispose();
    }
  }
}
