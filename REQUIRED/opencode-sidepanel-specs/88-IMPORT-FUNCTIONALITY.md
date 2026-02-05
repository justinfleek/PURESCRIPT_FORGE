# 88-IMPORT-FUNCTIONALITY: Data Import and Restore

## Overview

Import Functionality allows users to restore sessions, import settings, load recordings, and ingest external data into the sidepanel.

---

## Import Types

1. **Session Import** - Restore exported sessions (JSON/Markdown)
2. **Settings Import** - Restore configuration backup
3. **Recording Import** - Load session recordings
4. **Snapshot Import** - Restore state snapshots
5. **Bulk Import** - Import multiple items at once

---

## Visual Design

### Import Modal

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  IMPORT                                                              [✕]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ DROP FILES HERE ─────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │                                                                        │ │
│  │                        📁                                             │ │
│  │                                                                        │ │
│  │            Drag & drop files here, or click to browse                 │ │
│  │                                                                        │ │
│  │            Supported: .json, .md, .sidepanel                          │ │
│  │                                                                        │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ─── OR ───                                                                │
│                                                                             │
│  ┌─ IMPORT FROM ─────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  [📋 Clipboard]  [🔗 URL]  [💾 Local Storage Backup]                  │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ RECENT IMPORTS ──────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  📄 debug-auth-session.json          Jan 15, 2:30 PM         [Import] │ │
│  │  📄 sidepanel-settings.json          Jan 14, 10:00 AM        [Import] │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### File Preview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  IMPORT: debug-auth-session.json                                     [✕]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ FILE ANALYSIS ───────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Type:         Session Export                                         │ │
│  │  Version:      1.0                                                    │ │
│  │  Exported:     January 15, 2025 at 2:30 PM                           │ │
│  │  Size:         24.5 KB                                                │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ CONTENTS ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Session: "Debug Auth"                                                │ │
│  │  Messages: 12                                                         │ │
│  │  Total Tokens: 23,955                                                 │ │
│  │  Cost: $0.014                                                         │ │
│  │  Duration: 47 minutes                                                 │ │
│  │                                                                        │ │
│  │  Includes:                                                            │ │
│  │  ✓ Full message content                                               │ │
│  │  ✓ Timestamps                                                         │ │
│  │  ✓ Token counts                                                       │ │
│  │  ✓ Tool execution details                                             │ │
│  │  ✗ File contents (not included)                                       │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ IMPORT OPTIONS ──────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  [●] Import as new session                                            │ │
│  │  [ ] Merge with existing session                                      │ │
│  │  [ ] Replace current session                                          │ │
│  │                                                                        │ │
│  │  [✓] Mark as imported (shows badge)                                   │ │
│  │  [ ] Make this the active session                                     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  [Cancel]                                                    [Import]      │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Conflict Resolution

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ⚠ IMPORT CONFLICT                                                   [✕]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  A session with this ID already exists.                                    │
│                                                                             │
│  ┌─ COMPARISON ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │                  EXISTING              IMPORTING                      │ │
│  │  ─────────────────────────────────────────────────────────────────   │ │
│  │  Title         Debug Auth             Debug Auth                      │ │
│  │  Messages      12                     15                              │ │
│  │  Last Updated  Jan 15, 2:30 PM        Jan 15, 4:00 PM                │ │
│  │  Tokens        23,955                 28,432                          │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  What would you like to do?                                                │
│                                                                             │
│  [Keep Existing]  [Replace with Import]  [Keep Both]  [Merge]             │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Supported Formats

### Session JSON

```typescript
interface SessionImportJSON {
  version: string;
  exportedAt: string;
  session: {
    id: string;
    title: string;
    createdAt: string;
    model: string;
    messages: Message[];
    metrics: {
      promptTokens: number;
      completionTokens: number;
      cost: number;
    };
  };
}
```

### Settings JSON

```typescript
interface SettingsImportJSON {
  version: string;
  exportedAt: string;
  settings: {
    theme: 'dark' | 'light';
    keyboardShortcuts: Map<string, string>;
    notifications: NotificationSettings;
    defaultModel: string;
    // ... other settings
  };
}
```

### Sidepanel Bundle (.sidepanel)

```typescript
// Combined export with multiple items
interface SidepanelBundle {
  version: string;
  exportedAt: string;
  
  // Optional sections
  sessions?: SessionImportJSON[];
  settings?: SettingsImportJSON;
  recordings?: RecordingImportJSON[];
  snapshots?: SnapshotImportJSON[];
}
```

---

## Data Model

```typescript
interface ImportResult {
  success: boolean;
  type: ImportType;
  itemCount: number;
  warnings: ImportWarning[];
  errors: ImportError[];
  imported: ImportedItem[];
}

type ImportType = 
  | 'session'
  | 'settings'
  | 'recording'
  | 'snapshot'
  | 'bundle';

interface ImportWarning {
  code: string;
  message: string;
  field?: string;
}

interface ImportError {
  code: string;
  message: string;
  recoverable: boolean;
}

interface ImportedItem {
  type: ImportType;
  id: string;
  name: string;
  originalId?: string;  // If ID was changed
}

interface ImportOptions {
  conflictResolution: 'skip' | 'replace' | 'rename' | 'merge';
  validateSchema: boolean;
  markAsImported: boolean;
  setAsActive: boolean;
}
```

---

## Import Service

```typescript
// bridge/src/import/service.ts

export class ImportService {
  private db: Database;
  private validator: SchemaValidator;
  
  async importFile(file: File, options: ImportOptions): Promise<ImportResult> {
    // Read file
    const content = await this.readFile(file);
    
    // Detect type
    const type = this.detectType(content, file.name);
    
    // Validate
    if (options.validateSchema) {
      const validation = this.validator.validate(content, type);
      if (!validation.valid) {
        return {
          success: false,
          type,
          itemCount: 0,
          warnings: [],
          errors: validation.errors,
          imported: []
        };
      }
    }
    
    // Import based on type
    switch (type) {
      case 'session':
        return this.importSession(content, options);
      case 'settings':
        return this.importSettings(content, options);
      case 'recording':
        return this.importRecording(content, options);
      case 'bundle':
        return this.importBundle(content, options);
      default:
        return {
          success: false,
          type,
          itemCount: 0,
          warnings: [],
          errors: [{ code: 'UNKNOWN_TYPE', message: 'Unknown import type', recoverable: false }],
          imported: []
        };
    }
  }
  
  private async importSession(
    content: SessionImportJSON,
    options: ImportOptions
  ): Promise<ImportResult> {
    const warnings: ImportWarning[] = [];
    const imported: ImportedItem[] = [];
    
    // Check for existing
    const existing = await this.db.getSession(content.session.id);
    
    if (existing) {
      switch (options.conflictResolution) {
        case 'skip':
          warnings.push({
            code: 'SKIPPED',
            message: `Session "${content.session.title}" already exists, skipped`
          });
          return { success: true, type: 'session', itemCount: 0, warnings, errors: [], imported };
        
        case 'replace':
          await this.db.deleteSession(content.session.id);
          break;
        
        case 'rename':
          content.session.id = generateId();
          content.session.title = `${content.session.title} (imported)`;
          break;
        
        case 'merge':
          return this.mergeSession(existing, content.session, options);
      }
    }
    
    // Convert and save
    const session = this.convertSession(content.session);
    session.isImported = options.markAsImported;
    
    await this.db.saveSession(session);
    
    imported.push({
      type: 'session',
      id: session.id,
      name: session.title,
      originalId: content.session.id !== session.id ? content.session.id : undefined
    });
    
    // Set as active if requested
    if (options.setAsActive) {
      this.store.setCurrentSession(session);
    }
    
    return {
      success: true,
      type: 'session',
      itemCount: 1,
      warnings,
      errors: [],
      imported
    };
  }
  
  private detectType(content: any, filename: string): ImportType {
    // Check by content structure
    if (content.session && content.session.messages) return 'session';
    if (content.settings && content.settings.theme) return 'settings';
    if (content.recording && content.recording.events) return 'recording';
    if (content.sessions || content.recordings) return 'bundle';
    
    // Check by extension
    if (filename.endsWith('.sidepanel')) return 'bundle';
    
    return 'session';  // Default
  }
  
  async importFromClipboard(options: ImportOptions): Promise<ImportResult> {
    const text = await navigator.clipboard.readText();
    
    try {
      const content = JSON.parse(text);
      const type = this.detectType(content, 'clipboard');
      return this.importContent(content, type, options);
    } catch {
      // Try as Markdown
      const session = this.parseMarkdown(text);
      if (session) {
        return this.importSession(session, options);
      }
      
      return {
        success: false,
        type: 'session',
        itemCount: 0,
        warnings: [],
        errors: [{ code: 'PARSE_ERROR', message: 'Could not parse clipboard content', recoverable: false }],
        imported: []
      };
    }
  }
  
  async importFromUrl(url: string, options: ImportOptions): Promise<ImportResult> {
    try {
      const response = await fetch(url);
      const content = await response.json();
      const type = this.detectType(content, url);
      return this.importContent(content, type, options);
    } catch (error) {
      return {
        success: false,
        type: 'session',
        itemCount: 0,
        warnings: [],
        errors: [{ code: 'FETCH_ERROR', message: `Failed to fetch: ${error.message}`, recoverable: false }],
        imported: []
      };
    }
  }
}
```

---

## PureScript Component

```purescript
module Sidepanel.Components.Import where

type State =
  { isDragging :: Boolean
  , selectedFile :: Maybe File
  , preview :: Maybe ImportPreview
  , options :: ImportOptions
  , isImporting :: Boolean
  , result :: Maybe ImportResult
  }

data Action
  = DragEnter
  | DragLeave
  | Drop (Array File)
  | SelectFile File
  | SetOption String Boolean
  | SetConflictResolution ConflictResolution
  | Preview
  | PreviewLoaded ImportPreview
  | Import
  | ImportComplete ImportResult
  | ImportFromClipboard
  | ImportFromUrl String
  | Cancel

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "import-modal") ]
    [ case state.preview of
        Nothing -> renderDropZone state
        Just preview -> renderPreview state preview
    ]

renderDropZone :: forall m. State -> H.ComponentHTML Action () m
renderDropZone state =
  HH.div
    [ HP.classes $ dropZoneClasses state.isDragging
    , HE.onDragEnter \_ -> DragEnter
    , HE.onDragLeave \_ -> DragLeave
    , HE.onDrop handleDrop
    ]
    [ HH.div [ HP.class_ (H.ClassName "drop-zone__icon") ] [ HH.text "📁" ]
    , HH.div [ HP.class_ (H.ClassName "drop-zone__text") ]
        [ HH.text "Drag & drop files here, or "
        , HH.label
            [ HP.class_ (H.ClassName "drop-zone__browse") ]
            [ HH.text "browse"
            , HH.input
                [ HP.type_ HP.InputFile
                , HP.accept ".json,.md,.sidepanel"
                , HE.onFileChange handleFileSelect
                ]
            ]
        ]
    , HH.div [ HP.class_ (H.ClassName "drop-zone__formats") ]
        [ HH.text "Supported: .json, .md, .sidepanel" ]
    ]

renderPreview :: forall m. State -> ImportPreview -> H.ComponentHTML Action () m
renderPreview state preview =
  HH.div
    [ HP.class_ (H.ClassName "import-preview") ]
    [ renderFileInfo preview
    , renderContents preview
    , renderOptions state.options
    , renderActions state
    ]
```

---

## CSS Styling

```css
.drop-zone {
  border: 2px dashed var(--color-border-default);
  border-radius: 12px;
  padding: var(--space-8);
  text-align: center;
  transition: all var(--transition-fast);
  cursor: pointer;
}

.drop-zone:hover,
.drop-zone--dragging {
  border-color: var(--color-primary);
  background: var(--color-primary-dim);
}

.drop-zone__icon {
  font-size: 48px;
  margin-bottom: var(--space-4);
}

.drop-zone__text {
  font-size: var(--font-size-lg);
  color: var(--color-text-secondary);
  margin-bottom: var(--space-2);
}

.drop-zone__browse {
  color: var(--color-primary);
  cursor: pointer;
}

.drop-zone__browse input {
  display: none;
}

.drop-zone__formats {
  font-size: var(--font-size-sm);
  color: var(--color-text-tertiary);
}

.import-preview {
  padding: var(--space-4);
}

.import-preview__section {
  margin-bottom: var(--space-4);
  padding: var(--space-3);
  background: var(--color-bg-base);
  border-radius: 8px;
}
```

---

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| `Ctrl+I` | Open import modal |
| `Ctrl+V` | Import from clipboard (when modal open) |

---

## Related Specifications

- `86-EXPORT-FUNCTIONALITY.md` - Export counterpart
- `23-SESSION-MANAGEMENT.md` - Session handling
- `55-SETTINGS-PANEL.md` - Settings management

---

*"Your data travels with you. Import anywhere, continue seamlessly."*
