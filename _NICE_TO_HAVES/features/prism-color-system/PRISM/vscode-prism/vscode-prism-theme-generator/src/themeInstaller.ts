import * as vscode from "vscode";
import * as fs from "fs";
import * as path from "path";
import { ThemeVariant } from "./types";
import { ThemePreset, presetToVariant } from "./presetGallery";

/**
 * Theme Installer - Generates and installs VS Code themes
 * 
 * This module handles:
 * 1. Converting Base16 palettes to VS Code theme JSON
 * 2. Writing theme files to the extension's themes directory
 * 3. Registering themes with VS Code
 * 4. Applying themes without restart
 */

interface VSCodeTheme {
  name: string;
  type: "dark" | "light";
  colors: Record<string, string>;
  tokenColors: TokenColor[];
}

interface TokenColor {
  name?: string;
  scope: string | string[];
  settings: {
    foreground?: string;
    fontStyle?: string;
  };
}

/**
 * Convert Base16 palette to VS Code theme format
 */
export function base16ToVSCodeTheme(
  name: string,
  colors: Record<string, string>,
  mode: "dark" | "light"
): VSCodeTheme {
  const {
    base00, base01, base02, base03, base04, base05, base06, base07,
    base08, base09, base0A, base0B, base0C, base0D, base0E, base0F
  } = colors;

  return {
    name,
    type: mode,
    colors: {
      // Editor colors
      "editor.background": base00,
      "editor.foreground": base05,
      "editor.lineHighlightBackground": base01,
      "editor.selectionBackground": base02,
      "editor.selectionHighlightBackground": `${base02}80`,
      "editor.findMatchBackground": `${base0A}40`,
      "editor.findMatchHighlightBackground": `${base0A}25`,
      "editorCursor.foreground": base0A,
      "editorWhitespace.foreground": base03,
      "editorIndentGuide.background": base02,
      "editorIndentGuide.activeBackground": base03,
      "editorLineNumber.foreground": base03,
      "editorLineNumber.activeForeground": base0A,
      "editorRuler.foreground": base02,
      "editorBracketMatch.background": `${base0A}30`,
      "editorBracketMatch.border": base0A,
      
      // Editor gutter
      "editorGutter.background": base00,
      "editorGutter.modifiedBackground": base0D,
      "editorGutter.addedBackground": base0B,
      "editorGutter.deletedBackground": base08,
      
      // Editor widget
      "editorWidget.background": base01,
      "editorWidget.border": base02,
      "editorSuggestWidget.background": base01,
      "editorSuggestWidget.border": base02,
      "editorSuggestWidget.selectedBackground": base02,
      "editorSuggestWidget.highlightForeground": base0A,
      
      // Editor hover
      "editorHoverWidget.background": base01,
      "editorHoverWidget.border": base02,
      
      // Diff editor
      "diffEditor.insertedTextBackground": `${base0B}20`,
      "diffEditor.removedTextBackground": `${base08}20`,
      
      // Workbench
      "focusBorder": base0A,
      "foreground": base05,
      "widget.shadow": `${base00}80`,
      "selection.background": `${base0A}40`,
      "descriptionForeground": base04,
      "errorForeground": base08,
      
      // Activity bar
      "activityBar.background": base00,
      "activityBar.foreground": base05,
      "activityBar.inactiveForeground": base03,
      "activityBar.border": base01,
      "activityBarBadge.background": base0A,
      "activityBarBadge.foreground": base00,
      
      // Side bar
      "sideBar.background": base00,
      "sideBar.foreground": base05,
      "sideBar.border": base01,
      "sideBarTitle.foreground": base05,
      "sideBarSectionHeader.background": base01,
      "sideBarSectionHeader.foreground": base05,
      
      // List/Tree
      "list.activeSelectionBackground": base02,
      "list.activeSelectionForeground": base05,
      "list.inactiveSelectionBackground": base01,
      "list.inactiveSelectionForeground": base05,
      "list.hoverBackground": base01,
      "list.hoverForeground": base05,
      "list.focusBackground": base02,
      "list.focusForeground": base05,
      "list.highlightForeground": base0A,
      "list.errorForeground": base08,
      "list.warningForeground": base09,
      
      // Tree indent guides
      "tree.indentGuidesStroke": base02,
      
      // Status bar
      "statusBar.background": base01,
      "statusBar.foreground": base05,
      "statusBar.border": base02,
      "statusBar.debuggingBackground": base09,
      "statusBar.debuggingForeground": base00,
      "statusBar.noFolderBackground": base01,
      "statusBarItem.activeBackground": base02,
      "statusBarItem.hoverBackground": base02,
      "statusBarItem.prominentBackground": base02,
      "statusBarItem.prominentHoverBackground": base03,
      
      // Title bar
      "titleBar.activeBackground": base00,
      "titleBar.activeForeground": base05,
      "titleBar.inactiveBackground": base00,
      "titleBar.inactiveForeground": base04,
      "titleBar.border": base01,
      
      // Menu
      "menu.background": base01,
      "menu.foreground": base05,
      "menu.selectionBackground": base02,
      "menu.selectionForeground": base05,
      "menu.separatorBackground": base02,
      "menubar.selectionBackground": base02,
      "menubar.selectionForeground": base05,
      
      // Tabs
      "tab.activeBackground": base00,
      "tab.activeForeground": base05,
      "tab.activeBorder": base0A,
      "tab.inactiveBackground": base01,
      "tab.inactiveForeground": base04,
      "tab.border": base01,
      "tab.hoverBackground": base00,
      "tab.unfocusedActiveBackground": base00,
      "tab.unfocusedActiveForeground": base04,
      "editorGroupHeader.tabsBackground": base01,
      "editorGroupHeader.tabsBorder": base01,
      
      // Buttons
      "button.background": base0A,
      "button.foreground": base00,
      "button.hoverBackground": base0B,
      "button.secondaryBackground": base02,
      "button.secondaryForeground": base05,
      "button.secondaryHoverBackground": base03,
      
      // Input
      "input.background": base01,
      "input.foreground": base05,
      "input.border": base02,
      "input.placeholderForeground": base04,
      "inputOption.activeBackground": base02,
      "inputOption.activeBorder": base0A,
      "inputValidation.errorBackground": base01,
      "inputValidation.errorBorder": base08,
      "inputValidation.infoBackground": base01,
      "inputValidation.infoBorder": base0D,
      "inputValidation.warningBackground": base01,
      "inputValidation.warningBorder": base09,
      
      // Dropdown
      "dropdown.background": base01,
      "dropdown.foreground": base05,
      "dropdown.border": base02,
      "dropdown.listBackground": base01,
      
      // Scrollbar
      "scrollbar.shadow": `${base00}80`,
      "scrollbarSlider.background": `${base03}60`,
      "scrollbarSlider.hoverBackground": `${base03}80`,
      "scrollbarSlider.activeBackground": `${base03}a0`,
      
      // Badge
      "badge.background": base0A,
      "badge.foreground": base00,
      
      // Progress bar
      "progressBar.background": base0A,
      
      // Breadcrumb
      "breadcrumb.foreground": base04,
      "breadcrumb.focusForeground": base05,
      "breadcrumb.activeSelectionForeground": base05,
      "breadcrumbPicker.background": base01,
      
      // Notifications
      "notifications.background": base01,
      "notifications.foreground": base05,
      "notifications.border": base02,
      "notificationCenterHeader.background": base01,
      "notificationCenterHeader.foreground": base05,
      
      // Panel
      "panel.background": base00,
      "panel.border": base02,
      "panelTitle.activeBorder": base0A,
      "panelTitle.activeForeground": base05,
      "panelTitle.inactiveForeground": base04,
      
      // Terminal
      "terminal.background": base00,
      "terminal.foreground": base05,
      "terminal.ansiBlack": base00,
      "terminal.ansiRed": base08,
      "terminal.ansiGreen": base0B,
      "terminal.ansiYellow": base0A,
      "terminal.ansiBlue": base0D,
      "terminal.ansiMagenta": base0E,
      "terminal.ansiCyan": base0C,
      "terminal.ansiWhite": base05,
      "terminal.ansiBrightBlack": base03,
      "terminal.ansiBrightRed": base08,
      "terminal.ansiBrightGreen": base0B,
      "terminal.ansiBrightYellow": base0A,
      "terminal.ansiBrightBlue": base0D,
      "terminal.ansiBrightMagenta": base0E,
      "terminal.ansiBrightCyan": base0C,
      "terminal.ansiBrightWhite": base07,
      "terminalCursor.foreground": base0A,
      
      // Git decoration
      "gitDecoration.addedResourceForeground": base0B,
      "gitDecoration.modifiedResourceForeground": base0D,
      "gitDecoration.deletedResourceForeground": base08,
      "gitDecoration.untrackedResourceForeground": base0C,
      "gitDecoration.ignoredResourceForeground": base03,
      "gitDecoration.conflictingResourceForeground": base09,
      
      // Peek view
      "peekView.border": base0A,
      "peekViewEditor.background": base01,
      "peekViewEditorGutter.background": base01,
      "peekViewResult.background": base00,
      "peekViewResult.fileForeground": base05,
      "peekViewResult.lineForeground": base04,
      "peekViewResult.matchHighlightBackground": `${base0A}40`,
      "peekViewResult.selectionBackground": base02,
      "peekViewResult.selectionForeground": base05,
      "peekViewTitle.background": base01,
      "peekViewTitleDescription.foreground": base04,
      "peekViewTitleLabel.foreground": base05,
      
      // Minimap
      "minimap.background": base00,
      "minimap.selectionHighlight": `${base0A}60`,
      "minimap.errorHighlight": base08,
      "minimap.warningHighlight": base09,
      "minimap.findMatchHighlight": base0A,
      "minimapGutter.addedBackground": base0B,
      "minimapGutter.modifiedBackground": base0D,
      "minimapGutter.deletedBackground": base08,
      
      // Debug
      "debugToolBar.background": base01,
      "debugIcon.breakpointForeground": base08,
      "debugIcon.breakpointDisabledForeground": base03,
      "debugConsole.infoForeground": base0D,
      "debugConsole.warningForeground": base09,
      "debugConsole.errorForeground": base08,
    },
    tokenColors: [
      // Comments
      {
        name: "Comment",
        scope: ["comment", "punctuation.definition.comment"],
        settings: { foreground: base03, fontStyle: "italic" }
      },
      
      // Strings
      {
        name: "String",
        scope: ["string", "string.quoted"],
        settings: { foreground: base0B }
      },
      {
        name: "String escape",
        scope: ["constant.character.escape", "string.regexp"],
        settings: { foreground: base0C }
      },
      
      // Numbers and constants
      {
        name: "Number",
        scope: ["constant.numeric"],
        settings: { foreground: base09 }
      },
      {
        name: "Boolean",
        scope: ["constant.language.boolean"],
        settings: { foreground: base09 }
      },
      {
        name: "Constant",
        scope: ["constant", "constant.language", "support.constant"],
        settings: { foreground: base09 }
      },
      
      // Keywords
      {
        name: "Keyword",
        scope: ["keyword", "keyword.control", "keyword.operator.new"],
        settings: { foreground: base0E }
      },
      {
        name: "Keyword operator",
        scope: ["keyword.operator"],
        settings: { foreground: base05 }
      },
      {
        name: "Storage",
        scope: ["storage", "storage.type", "storage.modifier"],
        settings: { foreground: base0E }
      },
      
      // Functions
      {
        name: "Function",
        scope: ["entity.name.function", "support.function", "meta.function-call"],
        settings: { foreground: base0D }
      },
      {
        name: "Function parameter",
        scope: ["variable.parameter", "meta.parameter"],
        settings: { foreground: base05 }
      },
      
      // Variables
      {
        name: "Variable",
        scope: ["variable", "variable.other"],
        settings: { foreground: base05 }
      },
      {
        name: "Variable language",
        scope: ["variable.language"],
        settings: { foreground: base08 }
      },
      
      // Types - THE HERO COLOR
      {
        name: "Type",
        scope: [
          "entity.name.type",
          "entity.name.class",
          "support.type",
          "support.class",
          "entity.other.inherited-class"
        ],
        settings: { foreground: base0A }
      },
      {
        name: "Type parameter",
        scope: ["entity.name.type.parameter"],
        settings: { foreground: base0A, fontStyle: "italic" }
      },
      
      // Tags (HTML, JSX)
      {
        name: "Tag",
        scope: ["entity.name.tag", "punctuation.definition.tag"],
        settings: { foreground: base08 }
      },
      {
        name: "Tag attribute",
        scope: ["entity.other.attribute-name"],
        settings: { foreground: base0A }
      },
      
      // CSS
      {
        name: "CSS selector",
        scope: ["entity.other.attribute-name.class.css", "entity.other.attribute-name.id.css"],
        settings: { foreground: base0A }
      },
      {
        name: "CSS property",
        scope: ["support.type.property-name.css"],
        settings: { foreground: base0D }
      },
      {
        name: "CSS value",
        scope: ["support.constant.property-value.css"],
        settings: { foreground: base09 }
      },
      
      // JSON
      {
        name: "JSON key",
        scope: ["support.type.property-name.json"],
        settings: { foreground: base0D }
      },
      
      // Markdown
      {
        name: "Markdown heading",
        scope: [
          "markup.heading.markdown",
          "markup.heading",
          "entity.name.section.markdown"
        ],
        settings: { foreground: base0D, fontStyle: "bold" }
      },
      {
        name: "Markdown heading 1",
        scope: ["heading.1.markdown"],
        settings: { foreground: base0D, fontStyle: "bold" }
      },
      {
        name: "Markdown heading 2",
        scope: ["heading.2.markdown"],
        settings: { foreground: base0D, fontStyle: "bold" }
      },
      {
        name: "Markdown heading 3",
        scope: ["heading.3.markdown"],
        settings: { foreground: base0D, fontStyle: "bold" }
      },
      {
        name: "Markdown heading 4",
        scope: ["heading.4.markdown"],
        settings: { foreground: base0D, fontStyle: "bold" }
      },
      {
        name: "Markdown heading 5",
        scope: ["heading.5.markdown"],
        settings: { foreground: base0D, fontStyle: "bold" }
      },
      {
        name: "Markdown heading 6",
        scope: ["heading.6.markdown"],
        settings: { foreground: base0D, fontStyle: "bold" }
      },
      {
        name: "Markdown bold",
        scope: ["markup.bold"],
        settings: { fontStyle: "bold" }
      },
      {
        name: "Markdown italic",
        scope: ["markup.italic"],
        settings: { fontStyle: "italic" }
      },
      {
        name: "Markdown link",
        scope: ["markup.underline.link"],
        settings: { foreground: base0C }
      },
      {
        name: "Markdown code",
        scope: ["markup.inline.raw", "markup.fenced_code.block"],
        settings: { foreground: base0B }
      },
      
      // Punctuation
      {
        name: "Punctuation",
        scope: ["punctuation"],
        settings: { foreground: base05 }
      },
      {
        name: "Punctuation bracket",
        scope: ["punctuation.definition.bracket", "meta.brace"],
        settings: { foreground: base05 }
      },
      
      // Support
      {
        name: "Support",
        scope: ["support"],
        settings: { foreground: base0C }
      },
      
      // Invalid
      {
        name: "Invalid",
        scope: ["invalid", "invalid.illegal"],
        settings: { foreground: base08 }
      },
      {
        name: "Invalid deprecated",
        scope: ["invalid.deprecated"],
        settings: { foreground: base09 }
      },
      
      // Diff
      {
        name: "Diff inserted",
        scope: ["markup.inserted"],
        settings: { foreground: base0B }
      },
      {
        name: "Diff deleted",
        scope: ["markup.deleted"],
        settings: { foreground: base08 }
      },
      {
        name: "Diff changed",
        scope: ["markup.changed"],
        settings: { foreground: base0D }
      }
    ]
  };
}

/**
 * Write theme to file system and register with VS Code
 */
export async function installTheme(
  context: vscode.ExtensionContext,
  preset: ThemePreset
): Promise<void> {
  const variant = presetToVariant(preset);
  const theme = base16ToVSCodeTheme(
    `Prism ${preset.name}`,
    variant.colors,
    preset.mode
  );

  // Get themes directory in extension
  const themesDir = path.join(context.extensionPath, "themes");
  
  // Create themes directory if it doesn't exist
  if (!fs.existsSync(themesDir)) {
    fs.mkdirSync(themesDir, { recursive: true });
  }

  // Write theme file
  const themeFileName = `prism-${preset.id}.json`;
  const themePath = path.join(themesDir, themeFileName);
  fs.writeFileSync(themePath, JSON.stringify(theme, null, 2));

  // Apply theme immediately
  await vscode.workspace.getConfiguration().update(
    "workbench.colorTheme",
    `Prism ${preset.name}`,
    vscode.ConfigurationTarget.Global
  );

  vscode.window.showInformationMessage(`Theme "${preset.name}" installed and applied!`);
}

/**
 * Generate all preset themes at once
 */
export async function installAllPresets(
  context: vscode.ExtensionContext,
  presets: ThemePreset[]
): Promise<void> {
  const themesDir = path.join(context.extensionPath, "themes");
  
  if (!fs.existsSync(themesDir)) {
    fs.mkdirSync(themesDir, { recursive: true });
  }

  for (const preset of presets) {
    const variant = presetToVariant(preset);
    const theme = base16ToVSCodeTheme(
      `Prism ${preset.name}`,
      variant.colors,
      preset.mode
    );
    
    const themeFileName = `prism-${preset.id}.json`;
    const themePath = path.join(themesDir, themeFileName);
    fs.writeFileSync(themePath, JSON.stringify(theme, null, 2));
  }

  vscode.window.showInformationMessage(`Generated ${presets.length} Prism themes!`);
}

/**
 * Generate package.json contributes.themes entries
 */
export function generatePackageThemeContributions(presets: ThemePreset[]): object[] {
  return presets.map(preset => ({
    label: `Prism ${preset.name}`,
    uiTheme: preset.mode === "dark" ? "vs-dark" : "vs",
    path: `./themes/prism-${preset.id}.json`
  }));
}
