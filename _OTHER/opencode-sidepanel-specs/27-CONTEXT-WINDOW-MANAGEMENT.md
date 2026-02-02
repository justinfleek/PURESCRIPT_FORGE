# 27-CONTEXT-WINDOW-MANAGEMENT: Managing AI Context

## Overview

Context window management is critical for effective AI interactions. This document specifies how to track, optimize, and visualize the context window usage.

---

## Context Window Basics

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         CONTEXT WINDOW ANATOMY                              │
│                                                                              │
│  Total Context: 128,000 tokens (llama-3.3-70b)                             │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ SYSTEM PROMPT          │ FILE CONTEXT    │ HISTORY    │ OUTPUT     │   │
│  │ (~2,000 tokens)        │ (~20,000 tk)    │ (~40,000)  │ (reserved) │   │
│  │                        │                 │            │ (~8,000)   │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                              │
│  Used: 62,000 / 128,000 (48%)          Available: 66,000 tokens            │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Visual Design

### Context Usage Widget

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  CONTEXT WINDOW                                            62K / 128K (48%)│
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │████████████████████████████████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░│   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─ BREAKDOWN ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  📋 System Prompt          2,145 tk       ███░░░░░░░░░░         2%   │ │
│  │  📁 File Context          21,340 tk       ████████░░░░░        17%   │ │
│  │  💬 Conversation          38,515 tk       ████████████████     30%   │ │
│  │  🔧 Reserved for Output    8,000 tk       ███████░░░░░░░        6%   │ │
│  │  ─────────────────────────────────────────────────────────────────   │ │
│  │  ✨ Available             58,000 tk       ██████████████████   45%   │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  💡 Tip: Remove unused files to free up 8,234 tokens  [Optimize]          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Context Pressure Warning

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ⚠ CONTEXT PRESSURE                                       115K / 128K (90%)│
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │████████████████████████████████████████████████████████████████████░│   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Context is nearly full. Consider:                                         │
│                                                                             │
│  • Remove files from context (saves ~15K tokens)                           │
│  • Start a new session (keeps file context)                                │
│  • Summarize old messages                                                  │
│                                                                             │
│  [Remove Files]  [New Session]  [Summarize]                                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface ContextWindow {
  // Limits
  maxTokens: number;           // Model's max context
  reservedForOutput: number;   // Reserved for response
  
  // Current usage
  systemPromptTokens: number;
  fileContextTokens: number;
  conversationTokens: number;
  
  // Computed
  totalUsed: number;
  available: number;
  usagePercent: number;
  
  // Breakdown
  breakdown: ContextBreakdown[];
  
  // Status
  pressure: ContextPressure;
}

interface ContextBreakdown {
  category: ContextCategory;
  tokens: number;
  percent: number;
  items: ContextItem[];
}

type ContextCategory = 
  | 'system_prompt'
  | 'file_context'
  | 'conversation'
  | 'reserved'
  | 'available';

interface ContextItem {
  id: string;
  name: string;
  tokens: number;
  removable: boolean;
}

type ContextPressure = 
  | 'low'       // < 50%
  | 'moderate'  // 50-75%
  | 'high'      // 75-90%
  | 'critical'; // > 90%
```

---

## Context Manager

```typescript
// bridge/src/context/manager.ts

export class ContextManager {
  private modelLimits: Map<string, number> = new Map([
    ['llama-3.3-70b', 128000],
    ['llama-3.1-405b', 128000],
    ['qwen-2.5-72b', 128000],
    ['deepseek-r1-70b', 64000],
    ['qwen-2.5-32b', 64000],
    ['qwen-2.5-7b', 32000]
  ]);
  
  private reservedForOutput = 8000;
  
  calculateUsage(
    model: string,
    systemPrompt: string,
    files: FileContext[],
    messages: Message[]
  ): ContextWindow {
    const maxTokens = this.modelLimits.get(model) ?? 128000;
    
    // Calculate each component
    const systemPromptTokens = estimateTokens(systemPrompt);
    const fileContextTokens = files.reduce(
      (sum, f) => sum + estimateTokens(f.content), 0
    );
    const conversationTokens = messages.reduce(
      (sum, m) => sum + estimateTokens(m.content as string), 0
    );
    
    const totalUsed = systemPromptTokens + fileContextTokens + 
                      conversationTokens + this.reservedForOutput;
    const available = maxTokens - totalUsed;
    const usagePercent = (totalUsed / maxTokens) * 100;
    
    // Build breakdown
    const breakdown: ContextBreakdown[] = [
      {
        category: 'system_prompt',
        tokens: systemPromptTokens,
        percent: (systemPromptTokens / maxTokens) * 100,
        items: [{ id: 'system', name: 'System Prompt', tokens: systemPromptTokens, removable: false }]
      },
      {
        category: 'file_context',
        tokens: fileContextTokens,
        percent: (fileContextTokens / maxTokens) * 100,
        items: files.map(f => ({
          id: f.path,
          name: f.path,
          tokens: estimateTokens(f.content),
          removable: true
        }))
      },
      {
        category: 'conversation',
        tokens: conversationTokens,
        percent: (conversationTokens / maxTokens) * 100,
        items: messages.map((m, i) => ({
          id: `msg-${i}`,
          name: `${m.role}: ${(m.content as string).slice(0, 50)}...`,
          tokens: estimateTokens(m.content as string),
          removable: false
        }))
      },
      {
        category: 'reserved',
        tokens: this.reservedForOutput,
        percent: (this.reservedForOutput / maxTokens) * 100,
        items: []
      },
      {
        category: 'available',
        tokens: Math.max(0, available),
        percent: Math.max(0, (available / maxTokens) * 100),
        items: []
      }
    ];
    
    return {
      maxTokens,
      reservedForOutput: this.reservedForOutput,
      systemPromptTokens,
      fileContextTokens,
      conversationTokens,
      totalUsed,
      available: Math.max(0, available),
      usagePercent: Math.min(100, usagePercent),
      breakdown,
      pressure: this.getPressure(usagePercent)
    };
  }
  
  private getPressure(usagePercent: number): ContextPressure {
    if (usagePercent < 50) return 'low';
    if (usagePercent < 75) return 'moderate';
    if (usagePercent < 90) return 'high';
    return 'critical';
  }
  
  getOptimizations(context: ContextWindow): Optimization[] {
    const optimizations: Optimization[] = [];
    
    // Check for removable files
    const fileBreakdown = context.breakdown.find(b => b.category === 'file_context');
    if (fileBreakdown && fileBreakdown.tokens > 10000) {
      const largestFiles = fileBreakdown.items
        .filter(i => i.removable)
        .sort((a, b) => b.tokens - a.tokens)
        .slice(0, 3);
      
      if (largestFiles.length > 0) {
        optimizations.push({
          type: 'remove_files',
          description: `Remove ${largestFiles.length} large files`,
          tokensSaved: largestFiles.reduce((sum, f) => sum + f.tokens, 0),
          items: largestFiles.map(f => f.id)
        });
      }
    }
    
    // Suggest summarization if conversation is long
    const convBreakdown = context.breakdown.find(b => b.category === 'conversation');
    if (convBreakdown && convBreakdown.items.length > 20) {
      optimizations.push({
        type: 'summarize',
        description: 'Summarize older messages',
        tokensSaved: Math.floor(convBreakdown.tokens * 0.6),
        items: []
      });
    }
    
    // Suggest new session if very full
    if (context.pressure === 'critical') {
      optimizations.push({
        type: 'new_session',
        description: 'Start a new session (keeps file context)',
        tokensSaved: context.conversationTokens,
        items: []
      });
    }
    
    return optimizations;
  }
}

interface Optimization {
  type: 'remove_files' | 'summarize' | 'new_session';
  description: string;
  tokensSaved: number;
  items: string[];
}
```

---

## PureScript Component

```purescript
module Sidepanel.Components.ContextWindow where

type State =
  { context :: ContextWindow
  , showBreakdown :: Boolean
  , optimizations :: Array Optimization
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes $ contextClasses state.context.pressure ]
    [ renderHeader state.context
    , renderProgressBar state.context
    , when state.showBreakdown $ renderBreakdown state.context
    , when (state.context.pressure >= High) $ renderWarning state
    , when (not (null state.optimizations)) $ renderOptimizations state.optimizations
    ]

renderProgressBar :: forall m. ContextWindow -> H.ComponentHTML Action () m
renderProgressBar ctx =
  HH.div
    [ HP.class_ (H.ClassName "context-progress") ]
    [ HH.div
        [ HP.class_ (H.ClassName "context-progress__bar")
        , HP.style $ "width: " <> show ctx.usagePercent <> "%"
        ]
        []
    ]

renderBreakdown :: forall m. ContextWindow -> H.ComponentHTML Action () m
renderBreakdown ctx =
  HH.div
    [ HP.class_ (H.ClassName "context-breakdown") ]
    (map renderBreakdownItem ctx.breakdown)

renderBreakdownItem :: forall m. ContextBreakdown -> H.ComponentHTML Action () m
renderBreakdownItem item =
  HH.div
    [ HP.class_ (H.ClassName "breakdown-item") ]
    [ HH.span [ HP.class_ (H.ClassName "breakdown-icon") ]
        [ HH.text $ categoryIcon item.category ]
    , HH.span [ HP.class_ (H.ClassName "breakdown-name") ]
        [ HH.text $ categoryName item.category ]
    , HH.span [ HP.class_ (H.ClassName "breakdown-tokens") ]
        [ HH.text $ formatTokens item.tokens ]
    , HH.div [ HP.class_ (H.ClassName "breakdown-bar") ]
        [ HH.div
            [ HP.class_ (H.ClassName "breakdown-bar__fill")
            , HP.style $ "width: " <> show item.percent <> "%"
            ]
            []
        ]
    , HH.span [ HP.class_ (H.ClassName "breakdown-percent") ]
        [ HH.text $ show (round item.percent) <> "%" ]
    ]

categoryIcon :: ContextCategory -> String
categoryIcon = case _ of
  SystemPrompt -> "📋"
  FileContext -> "📁"
  Conversation -> "💬"
  Reserved -> "🔧"
  Available -> "✨"
```

---

## CSS Styling

```css
.context-window {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: var(--space-3);
}

.context-window--high,
.context-window--critical {
  border-color: var(--color-warning);
}

.context-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: var(--space-2);
}

.context-progress {
  height: 8px;
  background: var(--color-bg-base);
  border-radius: 4px;
  overflow: hidden;
  margin-bottom: var(--space-3);
}

.context-progress__bar {
  height: 100%;
  background: var(--color-primary);
  transition: width 0.3s ease;
}

.context-window--high .context-progress__bar {
  background: var(--color-warning);
}

.context-window--critical .context-progress__bar {
  background: var(--color-error);
}

.breakdown-item {
  display: grid;
  grid-template-columns: 24px 1fr auto 100px auto;
  gap: var(--space-2);
  align-items: center;
  padding: var(--space-2) 0;
  border-bottom: 1px solid var(--color-border-subtle);
}

.breakdown-bar {
  height: 6px;
  background: var(--color-bg-base);
  border-radius: 3px;
  overflow: hidden;
}

.breakdown-bar__fill {
  height: 100%;
  background: var(--color-text-tertiary);
}
```

---

## Related Specifications

- `58-FILE-CONTEXT-VIEW.md` - File context management
- `23-SESSION-MANAGEMENT.md` - Session handling
- `16-MODEL-SELECTION.md` - Model context limits

---

*"Know your context. Use it wisely."*
