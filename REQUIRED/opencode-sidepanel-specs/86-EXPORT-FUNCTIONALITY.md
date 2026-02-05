# 86-EXPORT-FUNCTIONALITY: Data Export and Sharing

## Overview

Export Functionality allows users to export sessions, reports, analytics, and recordings in various formats for sharing, archiving, and external analysis.

---

## Export Types

1. **Session Export** - Conversation history as Markdown/JSON
2. **Analytics Report** - Usage stats as PDF/CSV
3. **Recording Export** - Session replay as JSON/video
4. **Configuration Export** - Settings backup as JSON
5. **Diff Export** - Code changes as patch files

---

## Visual Design

### Export Modal

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  EXPORT                                                              [✕]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  What would you like to export?                                            │
│                                                                             │
│  ┌─ SESSION DATA ────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐    │ │
│  │  │  📝 Markdown     │  │  📄 JSON         │  │  📊 HTML Report  │    │ │
│  │  │                  │  │                  │  │                  │    │ │
│  │  │  Human-readable  │  │  Full data       │  │  Styled report   │    │ │
│  │  │  conversation    │  │  with metadata   │  │  with charts     │    │ │
│  │  │                  │  │                  │  │                  │    │ │
│  │  │  [Export]        │  │  [Export]        │  │  [Export]        │    │ │
│  │  └──────────────────┘  └──────────────────┘  └──────────────────┘    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ ANALYTICS ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐    │ │
│  │  │  📈 CSV          │  │  📊 PDF Report   │  │  🔧 API Format   │    │ │
│  │  │                  │  │                  │  │                  │    │ │
│  │  │  Spreadsheet     │  │  Visual report   │  │  Machine-        │    │ │
│  │  │  compatible      │  │  with graphs     │  │  readable        │    │ │
│  │  │                  │  │                  │  │                  │    │ │
│  │  │  [Export]        │  │  [Export]        │  │  [Export]        │    │ │
│  │  └──────────────────┘  └──────────────────┘  └──────────────────┘    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ OTHER ───────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐    │ │
│  │  │  ⚙ Settings      │  │  🎬 Recording    │  │  📝 Diff/Patch   │    │ │
│  │  │                  │  │                  │  │                  │    │ │
│  │  │  Backup your     │  │  Export session  │  │  Code changes    │    │ │
│  │  │  configuration   │  │  recording       │  │  as patch file   │    │ │
│  │  │                  │  │                  │  │                  │    │ │
│  │  │  [Export]        │  │  [Export]        │  │  [Export]        │    │ │
│  │  └──────────────────┘  └──────────────────┘  └──────────────────┘    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Session Export Options

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  EXPORT SESSION: Debug Auth                                          [✕]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Format: [Markdown ▼]                                                      │
│                                                                             │
│  ┌─ OPTIONS ─────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  [✓] Include message content                                          │ │
│  │  [✓] Include timestamps                                               │ │
│  │  [✓] Include token counts                                             │ │
│  │  [ ] Include tool execution details                                   │ │
│  │  [ ] Include file contents (large)                                    │ │
│  │  [✓] Include cost breakdown                                           │ │
│  │                                                                        │ │
│  │  Message range:                                                       │ │
│  │  [All Messages ▼]  or  From #[1] To #[12]                            │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ PREVIEW ─────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  # Debug Auth Session                                                 │ │
│  │                                                                        │ │
│  │  **Date:** January 15, 2025                                           │ │
│  │  **Duration:** 47 minutes                                             │ │
│  │  **Model:** llama-3.3-70b                                             │ │
│  │  **Total Tokens:** 23,955                                             │ │
│  │  **Cost:** $0.014 (0.014 Diem)                                        │ │
│  │                                                                        │ │
│  │  ---                                                                   │ │
│  │                                                                        │ │
│  │  ## Conversation                                                       │ │
│  │                                                                        │ │
│  │  ### 12:30 PM - User                                                  │ │
│  │  Help me debug this authentication flow...                            │ │
│  │                                                      [Show More ▼]    │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Estimated size: 24 KB                                                     │
│                                                                             │
│  [Cancel]                                        [Copy to Clipboard]       │
│                                                  [Download File]           │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Export Formats

### Markdown Session Export

```markdown
# Debug Auth Session

**Date:** January 15, 2025
**Duration:** 47 minutes
**Model:** llama-3.3-70b (Venice)
**Total Tokens:** 23,955 (15,234 in / 8,721 out)
**Cost:** $0.014

---

## Summary

Fixed timezone bug in token expiration check. Added comprehensive tests.

## Conversation

### 12:30 PM - User
Help me debug this authentication flow. Users are getting logged out randomly.

### 12:30 PM - Assistant (1,234 → 567 tokens, $0.002)
I'll analyze the authentication code. Let me start by reading the relevant files.

**Tools Used:**
- `read_file`: src/auth/session.ts (45ms)
- `read_file`: src/auth/middleware.ts (32ms)

### 12:31 PM - Assistant (2,456 → 1,234 tokens, $0.004)
I found the issue. In session.ts line 42, the token expiration check is using local time instead of UTC...

[Full response truncated]

---

## Files Modified

- `src/auth/session.ts` - Fixed timezone bug
- `src/auth/session.test.ts` - Added test coverage

## Metrics

| Metric | Value |
|--------|-------|
| Messages | 12 |
| User Messages | 5 |
| Assistant Messages | 7 |
| Tool Calls | 8 |
| Files Read | 6 |
| Files Written | 2 |
```

### JSON Session Export

```json
{
  "version": "1.0",
  "exportedAt": "2025-01-15T15:45:00Z",
  "session": {
    "id": "sess_abc123",
    "title": "Debug Auth",
    "createdAt": "2025-01-15T12:30:00Z",
    "duration": 2820000,
    "model": "llama-3.3-70b",
    "provider": "venice",
    "metrics": {
      "promptTokens": 15234,
      "completionTokens": 8721,
      "totalTokens": 23955,
      "cost": 0.014,
      "messageCount": 12,
      "toolCalls": 8
    },
    "messages": [
      {
        "id": "msg_001",
        "role": "user",
        "content": "Help me debug this authentication flow...",
        "timestamp": "2025-01-15T12:30:00Z"
      },
      {
        "id": "msg_002",
        "role": "assistant",
        "content": "I'll analyze the authentication code...",
        "timestamp": "2025-01-15T12:30:15Z",
        "usage": {
          "promptTokens": 1234,
          "completionTokens": 567
        },
        "toolCalls": [
          {
            "name": "read_file",
            "args": { "path": "src/auth/session.ts" },
            "duration": 45
          }
        ]
      }
    ]
  }
}
```

### CSV Analytics Export

```csv
timestamp,type,model,prompt_tokens,completion_tokens,cost_diem,session_id
2025-01-15T12:30:00Z,message,llama-3.3-70b,1234,567,0.002,sess_abc123
2025-01-15T12:30:30Z,message,llama-3.3-70b,2456,1234,0.004,sess_abc123
2025-01-15T12:31:00Z,message,llama-3.3-70b,3567,2345,0.006,sess_abc123
```

---

## Data Model

```typescript
interface ExportOptions {
  format: ExportFormat;
  includeMessages: boolean;
  includeTimestamps: boolean;
  includeTokenCounts: boolean;
  includeToolDetails: boolean;
  includeFileContents: boolean;
  includeCostBreakdown: boolean;
  messageRange?: { start: number; end: number };
}

type ExportFormat = 
  | 'markdown'
  | 'json'
  | 'html'
  | 'csv'
  | 'pdf'
  | 'patch';

interface ExportResult {
  format: ExportFormat;
  filename: string;
  mimeType: string;
  content: string | Blob;
  sizeBytes: number;
}
```

---

## Export Service

```typescript
// bridge/src/export/service.ts

export class ExportService {
  
  async exportSession(
    sessionId: string,
    options: ExportOptions
  ): Promise<ExportResult> {
    const session = await this.db.getSession(sessionId);
    
    switch (options.format) {
      case 'markdown':
        return this.exportAsMarkdown(session, options);
      case 'json':
        return this.exportAsJson(session, options);
      case 'html':
        return this.exportAsHtml(session, options);
      default:
        throw new Error(`Unsupported format: ${options.format}`);
    }
  }
  
  private exportAsMarkdown(session: Session, options: ExportOptions): ExportResult {
    let md = `# ${session.title}\n\n`;
    
    // Metadata
    md += `**Date:** ${formatDate(session.createdAt)}\n`;
    md += `**Duration:** ${formatDuration(session.duration)}\n`;
    md += `**Model:** ${session.model}\n`;
    
    if (options.includeTokenCounts) {
      md += `**Total Tokens:** ${session.promptTokens + session.completionTokens}\n`;
    }
    
    if (options.includeCostBreakdown) {
      md += `**Cost:** $${session.cost.toFixed(3)}\n`;
    }
    
    md += `\n---\n\n## Conversation\n\n`;
    
    // Messages
    const messages = options.messageRange
      ? session.messages.slice(options.messageRange.start, options.messageRange.end + 1)
      : session.messages;
    
    for (const msg of messages) {
      if (options.includeTimestamps) {
        md += `### ${formatTime(msg.timestamp)} - ${capitalize(msg.role)}\n`;
      } else {
        md += `### ${capitalize(msg.role)}\n`;
      }
      
      md += `${msg.content}\n\n`;
      
      if (options.includeToolDetails && msg.toolCalls?.length) {
        md += `**Tools Used:**\n`;
        for (const tool of msg.toolCalls) {
          md += `- \`${tool.name}\`: ${tool.args.path ?? JSON.stringify(tool.args)}\n`;
        }
        md += '\n';
      }
    }
    
    return {
      format: 'markdown',
      filename: `${slugify(session.title)}-${formatDateCompact(session.createdAt)}.md`,
      mimeType: 'text/markdown',
      content: md,
      sizeBytes: new Blob([md]).size
    };
  }
  
  async exportAnalytics(
    dateRange: DateRange,
    format: 'csv' | 'pdf' | 'json'
  ): Promise<ExportResult> {
    const data = await this.db.getAnalytics(dateRange);
    
    switch (format) {
      case 'csv':
        return this.analyticsToCSV(data);
      case 'pdf':
        return this.analyticsToPDF(data);
      case 'json':
        return this.analyticsToJSON(data);
    }
  }
  
  exportSettings(): ExportResult {
    const settings = this.store.getState().settings;
    const json = JSON.stringify(settings, null, 2);
    
    return {
      format: 'json',
      filename: `sidepanel-settings-${formatDateCompact(new Date())}.json`,
      mimeType: 'application/json',
      content: json,
      sizeBytes: new Blob([json]).size
    };
  }
  
  async exportDiff(sessionId: string): Promise<ExportResult> {
    const changes = await this.db.getFileChanges(sessionId);
    
    let patch = '';
    for (const change of changes) {
      patch += `--- a/${change.path}\n`;
      patch += `+++ b/${change.path}\n`;
      patch += change.diff;
      patch += '\n';
    }
    
    return {
      format: 'patch',
      filename: `changes-${sessionId}.patch`,
      mimeType: 'text/x-diff',
      content: patch,
      sizeBytes: new Blob([patch]).size
    };
  }
}
```

---

## PureScript Component

```purescript
module Sidepanel.Components.Export where

data ExportFormat
  = Markdown
  | JSON
  | HTML
  | CSV
  | PDF
  | Patch

type ExportOptions =
  { format :: ExportFormat
  , includeMessages :: Boolean
  , includeTimestamps :: Boolean
  , includeTokenCounts :: Boolean
  , includeToolDetails :: Boolean
  , includeCostBreakdown :: Boolean
  }

type State =
  { exportType :: ExportType
  , options :: ExportOptions
  , preview :: Maybe String
  , isExporting :: Boolean
  , result :: Maybe ExportResult
  }

data ExportType
  = SessionExport String  -- session ID
  | AnalyticsExport
  | SettingsExport
  | RecordingExport String

data Action
  = SetExportType ExportType
  | SetFormat ExportFormat
  | ToggleOption String
  | GeneratePreview
  | PreviewGenerated String
  | Export
  | ExportComplete ExportResult
  | CopyToClipboard
  | DownloadFile
  | Close
```

---

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| `Ctrl+Shift+E` | Open export modal |
| `Ctrl+Shift+C` | Quick copy session as Markdown |

---

## Related Specifications

- `54-SESSION-PANEL.md` - Session data source
- `65-SESSION-RECORDING.md` - Recording export
- `55-SETTINGS-PANEL.md` - Settings backup

---

*"Your data is yours. Export it, share it, own it."*
