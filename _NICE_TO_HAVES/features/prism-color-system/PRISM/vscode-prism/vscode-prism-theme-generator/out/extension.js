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
exports.activate = activate;
exports.deactivate = deactivate;
const vscode = __importStar(require("vscode"));
const themeGeneratorPanel_1 = require("./themeGeneratorPanel");
const themePreviewPanel_1 = require("./themePreviewPanel");
const themeGeneratorPanelV2_1 = require("./themeGeneratorPanelV2");
const prism211Generator_1 = require("./prism211Generator");
const presetGallery_1 = require("./presetGallery");
const themeInstaller_1 = require("./themeInstaller");
// Status bar item for quick access
let statusBarItem;
function activate(context) {
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
    const open211Generator = vscode.commands.registerCommand("prismTheme.open211Generator", () => {
        prism211Generator_1.Prism211GeneratorPanel.createOrShow(context);
    });
    context.subscriptions.push(open211Generator);
    // =====================================================================
    // NEW: Open Premium Theme Gallery (Luxury UI)
    // =====================================================================
    const openGallery = vscode.commands.registerCommand("prismTheme.openGallery", () => {
        themeGeneratorPanelV2_1.ThemeGeneratorPanelV2.createOrShow(context);
    });
    // =====================================================================
    // LEGACY: Open Classic Generator
    // =====================================================================
    const generateCommand = vscode.commands.registerCommand("prismTheme.generate", () => {
        themeGeneratorPanel_1.ThemeGeneratorPanel.createOrShow(context.extensionUri);
    });
    // =====================================================================
    // Preview Theme
    // =====================================================================
    const previewCommand = vscode.commands.registerCommand("prismTheme.preview", () => {
        themePreviewPanel_1.ThemePreviewPanel.createOrShow(context.extensionUri);
    });
    // =====================================================================
    // NEW: Quick Apply Preset via Command Palette
    // =====================================================================
    const applyPreset = vscode.commands.registerCommand("prismTheme.applyPreset", async (presetId) => {
        if (!presetId) {
            // Show quick pick with all presets
            const items = presetGallery_1.ALL_PRESETS.map(p => ({
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
            const preset = (0, presetGallery_1.getPresetById)(presetId);
            if (preset) {
                await (0, themeInstaller_1.installTheme)(context, preset);
            }
            else {
                vscode.window.showErrorMessage(`Preset "${presetId}" not found`);
            }
        }
    });
    // =====================================================================
    // NEW: Browse Themes by Category
    // =====================================================================
    const browseCategory = vscode.commands.registerCommand("prismTheme.browseCategory", async () => {
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
            const presets = presetGallery_1.ALL_PRESETS.filter(p => p.category === selected.category);
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
                const preset = (0, presetGallery_1.getPresetById)(theme.presetId);
                if (preset) {
                    await (0, themeInstaller_1.installTheme)(context, preset);
                }
            }
        }
    });
    // =====================================================================
    // NEW: Generate All Theme Files
    // =====================================================================
    const generateAll = vscode.commands.registerCommand("prismTheme.generateAllThemes", async () => {
        const confirm = await vscode.window.showWarningMessage(`Generate ${presetGallery_1.ALL_PRESETS.length} Prism theme files?`, "Yes", "No");
        if (confirm === "Yes") {
            await (0, themeInstaller_1.installAllPresets)(context, presetGallery_1.ALL_PRESETS);
        }
    });
    // =====================================================================
    // Export Theme (TODO)
    // =====================================================================
    const exportCommand = vscode.commands.registerCommand("prismTheme.export", async () => {
        const themeData = await vscode.window.showInputBox({
            prompt: "Enter theme name",
            placeHolder: "my-custom-theme"
        });
        if (themeData) {
            vscode.window.showInformationMessage("Export coming soon! For now, themes are saved to the extension's themes/ directory.");
        }
    });
    // Register all commands
    context.subscriptions.push(openGallery, generateCommand, previewCommand, applyPreset, browseCategory, generateAll, exportCommand);
    // Show welcome message on first install
    const hasShownWelcome = context.globalState.get("prism.hasShownWelcome");
    if (!hasShownWelcome) {
        vscode.window.showInformationMessage("Prism installed! Create your perfect theme from a single hue.", "Open 211° Generator", "Browse Gallery").then(selection => {
            if (selection === "Open 211° Generator") {
                vscode.commands.executeCommand("prismTheme.open211Generator");
            }
            else if (selection === "Browse Gallery") {
                vscode.commands.executeCommand("prismTheme.openGallery");
            }
        });
        context.globalState.update("prism.hasShownWelcome", true);
    }
}
function deactivate() {
    if (statusBarItem) {
        statusBarItem.dispose();
    }
}
function getCategoryIcon(category) {
    const icons = {
        luxury: "$(star-full)",
        glass: "$(mirror)",
        bento: "$(layout)",
        neumorphism: "$(circle-outline)",
        responsive: "$(pulse)",
        easter_eggs: "$(gift)"
    };
    return icons[category] || "$(paintcan)";
}
//# sourceMappingURL=extension.js.map