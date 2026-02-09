import * as vscode from "vscode";
import { ThemeGeneratorPanel } from "./themeGeneratorPanel";
import { ThemePreviewPanel } from "./themePreviewPanel";
import { ThemeGeneratorPanelV2 } from "./themeGeneratorPanelV2";
import { Prism211GeneratorPanel } from "./prism211Generator";
import { ALL_PRESETS, getPresetById } from "./presetGallery";
import { installTheme, installAllPresets } from "./themeInstaller";

// Status bar item for quick access
let statusBarItem: vscode.StatusBarItem;

export function activate(context: vscode.ExtensionContext) {
  console.log("Prism Theme Generator extension is now active");

  // =====================================================================
  // STATUS BAR: Always-visible prism icon
  // =====================================================================
  statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
  statusBarItem.text = "$(symbol-color) 211°";
  statusBarItem.tooltip = "Open Prism 211° Color Generator";
  statusBarItem.command = "prismTheme.open211Generator";
  statusBarItem.show();
  context.subscriptions.push(statusBarItem);

  // =====================================================================
  // MAIN: Open 211° Generator (the core feature)
  // =====================================================================
  const open211Generator = vscode.commands.registerCommand(
    "prismTheme.open211Generator",
    () => {
      Prism211GeneratorPanel.createOrShow(context);
    }
  );
  context.subscriptions.push(open211Generator);

  // =====================================================================
  // NEW: Open Premium Theme Gallery (Luxury UI)
  // =====================================================================
  const openGallery = vscode.commands.registerCommand(
    "prismTheme.openGallery",
    () => {
      ThemeGeneratorPanelV2.createOrShow(context);
    }
  );

  // =====================================================================
  // LEGACY: Open Classic Generator
  // =====================================================================
  const generateCommand = vscode.commands.registerCommand(
    "prismTheme.generate",
    () => {
      ThemeGeneratorPanel.createOrShow(context.extensionUri);
    }
  );

  // =====================================================================
  // Preview Theme
  // =====================================================================
  const previewCommand = vscode.commands.registerCommand(
    "prismTheme.preview",
    () => {
      ThemePreviewPanel.createOrShow(context.extensionUri);
    }
  );

  // =====================================================================
  // NEW: Quick Apply Preset via Command Palette
  // =====================================================================
  const applyPreset = vscode.commands.registerCommand(
    "prismTheme.applyPreset",
    async (presetId?: string) => {
      if (!presetId) {
        // Show quick pick with all presets
        const items = ALL_PRESETS.map(p => ({
          label: getCategoryIcon(p.category) + " " + p.name,
          description: p.category,
          detail: p.inspiration,
          presetId: p.id
        }));

        const selected = await vscode.window.showQuickPick(items, {
          placeHolder: "Select a Prism Premium theme",
          matchOnDescription: true,
          matchOnDetail: true
        });

        if (selected) {
          presetId = selected.presetId;
        }
      }

      if (presetId) {
        const preset = getPresetById(presetId);
        if (preset) {
          await installTheme(context, preset);
        } else {
          vscode.window.showErrorMessage(`Preset "${presetId}" not found`);
        }
      }
    }
  );

  // =====================================================================
  // NEW: Browse Themes by Category
  // =====================================================================
  const browseCategory = vscode.commands.registerCommand(
    "prismTheme.browseCategory",
    async () => {
      const categories = [
        { label: "$(star-full) Luxury Marble", description: "Black marble, gold veining, obsidian", category: "luxury" },
        { label: "$(mirror) Glassmorphism", description: "Frosted glass with blur effects", category: "glass" },
        { label: "$(layout) Bento", description: "Floating card layouts", category: "bento" },
        { label: "$(circle-outline) Neumorphism", description: "Soft shadows, tactile depth", category: "neumorphism" },
        { label: "$(pulse) Responsive", description: "Themes that respond to activity", category: "responsive" },
        { label: "$(gift) Easter Eggs", description: "Hidden delights and rewards", category: "easter_eggs" }
      ];

      const selected = await vscode.window.showQuickPick(categories, {
        placeHolder: "Select a theme category"
      });

      if (selected) {
        const presets = ALL_PRESETS.filter(p => p.category === selected.category);
        const items = presets.map(p => ({
          label: p.name,
          description: p.tags.slice(0, 3).join(", "),
          detail: p.inspiration,
          presetId: p.id
        }));

        const theme = await vscode.window.showQuickPick(items, {
          placeHolder: `Select a ${selected.label.replace(/\$\([^)]+\)\s*/, '')} theme`
        });

        if (theme) {
          const preset = getPresetById(theme.presetId);
          if (preset) {
            await installTheme(context, preset);
          }
        }
      }
    }
  );

  // =====================================================================
  // NEW: Generate All Theme Files
  // =====================================================================
  const generateAll = vscode.commands.registerCommand(
    "prismTheme.generateAllThemes",
    async () => {
      const confirm = await vscode.window.showWarningMessage(
        `Generate ${ALL_PRESETS.length} Prism theme files?`,
        "Yes", "No"
      );
      
      if (confirm === "Yes") {
        await installAllPresets(context, ALL_PRESETS);
      }
    }
  );

  // =====================================================================
  // Export Theme (TODO)
  // =====================================================================
  const exportCommand = vscode.commands.registerCommand(
    "prismTheme.export",
    async () => {
      const themeData = await vscode.window.showInputBox({
        prompt: "Enter theme name",
        placeHolder: "my-custom-theme"
      });
      if (themeData) {
        vscode.window.showInformationMessage(
          "Export coming soon! For now, themes are saved to the extension's themes/ directory."
        );
      }
    }
  );

  // Register all commands
  context.subscriptions.push(
    openGallery,
    generateCommand,
    previewCommand,
    applyPreset,
    browseCategory,
    generateAll,
    exportCommand
  );

  // Show welcome message on first install
  const hasShownWelcome = context.globalState.get("prism.hasShownWelcome");
  if (!hasShownWelcome) {
    vscode.window.showInformationMessage(
      "Prism installed! Create your perfect theme from a single hue.",
      "Open 211° Generator",
      "Browse Gallery"
    ).then(selection => {
      if (selection === "Open 211° Generator") {
        vscode.commands.executeCommand("prismTheme.open211Generator");
      } else if (selection === "Browse Gallery") {
        vscode.commands.executeCommand("prismTheme.openGallery");
      }
    });
    context.globalState.update("prism.hasShownWelcome", true);
  }
}

export function deactivate() {
  if (statusBarItem) {
    statusBarItem.dispose();
  }
}

function getCategoryIcon(category: string): string {
  const icons: Record<string, string> = {
    luxury: "$(star-full)",
    glass: "$(mirror)",
    bento: "$(layout)",
    neumorphism: "$(circle-outline)",
    responsive: "$(pulse)",
    easter_eggs: "$(gift)"
  };
  return icons[category] || "$(paintcan)";
}
