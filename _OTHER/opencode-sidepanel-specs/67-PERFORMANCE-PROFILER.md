# 67-PERFORMANCE-PROFILER: Session Analytics and Flame Graphs

## Overview

The Performance Profiler provides deep visibility into where time is spent during AI coding sessions. It includes flame graphs, timing breakdowns, and optimization suggestions.

---

## Why Performance Profiling?

Power users ask:
- "Why did that response take so long?"
- "Where is my token budget going?"
- "Which tools are slow?"
- "How can I optimize my prompting?"

---

## Visual Design

### Performance Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  PERFORMANCE                                    Session: Debug Auth (47 min)│
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ SUMMARY ─────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Total Time        AI Thinking       Tool Execution     Network        │ │
│  │  47m 12s           29m 14s (62%)     11m 48s (25%)      6m 10s (13%)  │ │
│  │                                                                        │ │
│  │  Total Tokens      Avg Response      Messages           Tool Calls     │ │
│  │  23,955            1,996 tk          12                 8              │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ TIME BREAKDOWN ──────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ████████████████████████████████████████████████░░░░░░░░  AI (62%)   │ │
│  │  ████████████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  Tools(25%) │ │
│  │  ██████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  Net (13%)  │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ FLAME GRAPH ─────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │ │
│  │  │              Session: Debug Auth (47:12)                         │  │ │
│  │  ├─────────────────────────────────────┬───────────────────────────┤  │ │
│  │  │     AI Response #1 (5:23)           │    AI Response #2 (8:45)  │  │ │
│  │  ├─────────────┬───────────────────────┼─────────────┬─────────────┤  │ │
│  │  │  read_file  │    read_file          │  write_file │  AI #3      │  │ │
│  │  │  (0:45)     │    (0:32)             │  (4:12)     │  (12:34)    │  │ │
│  │  ├──────┬──────┼──────┬────────────────┼──────┬──────┼─────────────┤  │ │
│  │  │sess. │middle│ types│                │ Auth │ test │             │  │ │
│  │  │.ts   │ware  │ .ts  │                │ .tsx │ .tsx │             │  │ │
│  │  └──────┴──────┴──────┴────────────────┴──────┴──────┴─────────────┘  │ │
│  │                                                                        │ │
│  │  Hover for details • Click to zoom • Scroll to pan                    │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ SLOWEST OPERATIONS ──────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  1. AI Response #5        12:34   "Here's the complete test file..."  │ │
│  │     💡 Large output (4,521 tokens). Consider asking for incremental.  │ │
│  │                                                                        │ │
│  │  2. write_file             4:12   Auth.test.tsx (2,345 bytes)         │ │
│  │     💡 Large file write. Normal for test files.                       │ │
│  │                                                                        │ │
│  │  3. AI Response #2         8:45   "I found the issue in session.ts"   │ │
│  │     💡 Complex reasoning about multiple files.                        │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ OPTIMIZATION SUGGESTIONS ────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ⚡ Use smaller model for simple tasks                                │ │
│  │     3 responses could have used a faster model (-40% time est.)       │ │
│  │                                                                        │ │
│  │  ⚡ Batch file reads                                                   │ │
│  │     4 sequential reads could be batched (-15% time est.)              │ │
│  │                                                                        │ │
│  │  ⚡ More specific prompts                                              │ │
│  │     2 responses were overly verbose. Be more specific.                │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Token Breakdown

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  TOKEN ANALYSIS                                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ BY MESSAGE ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  MSG   INPUT    OUTPUT   TOTAL    COST     CONTENT                    │ │
│  │  ─────────────────────────────────────────────────────────────────   │ │
│  │  #1    234      0        234      $0.000   "Help me debug..."        │ │
│  │  #2    1,567    892      2,459    $0.002   "I'll analyze..."         │ │
│  │  #3    3,456    1,234    4,690    $0.003   "Found the issue..."      │ │
│  │  #4    312      0        312      $0.000   "Can you fix it?"         │ │
│  │  #5    5,678    4,521    10,199   $0.007   "Here's the fix..."       │ │
│  │  ...                                                                  │ │
│  │                                                                        │ │
│  │  TOTAL 15,234   8,721    23,955   $0.014                             │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ BY FILE IN CONTEXT ──────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  FILE                              TOKENS    % OF INPUT               │ │
│  │  ─────────────────────────────────────────────────────────────────   │ │
│  │  src/auth/session.ts               1,234     8.1%                     │ │
│  │  src/auth/middleware.ts              892     5.9%                     │ │
│  │  src/auth/types.ts                   234     1.5%                     │ │
│  │  src/components/Auth.tsx             567     3.7%                     │ │
│  │  src/components/Auth.test.tsx        421     2.8%                     │ │
│  │  (conversation history)           11,886    78.0%                     │ │
│  │                                                                        │ │
│  │  💡 78% of input tokens are conversation history.                     │ │
│  │     Consider starting a new session for unrelated tasks.              │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ BY MODEL ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ████████████████████████████████████████████████  llama-3.3-70b      │ │
│  │  │                                               │  23,955 tk (100%)  │ │
│  │  │                                               │  $0.014            │ │
│  │  └───────────────────────────────────────────────┘                    │ │
│  │                                                                        │ │
│  │  💡 Consider using a smaller model for simple queries.                │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface PerformanceData {
  sessionId: string;
  
  // Summary metrics
  totalDuration: number;  // ms
  aiThinkingTime: number;
  toolExecutionTime: number;
  networkTime: number;
  
  totalTokens: number;
  totalCost: number;
  messageCount: number;
  toolCallCount: number;
  
  // Detailed breakdowns
  events: TimedEvent[];
  
  // Analysis
  slowestOperations: SlowOperation[];
  suggestions: OptimizationSuggestion[];
}

interface TimedEvent {
  id: string;
  type: EventType;
  name: string;
  startTime: number;  // ms from session start
  endTime: number;
  duration: number;
  
  // Nested events (for flame graph)
  children: TimedEvent[];
  
  // Event-specific data
  metadata: EventMetadata;
}

type EventType = 
  | 'ai_response'
  | 'tool_execution'
  | 'file_read'
  | 'file_write'
  | 'network_request'
  | 'user_input';

interface EventMetadata {
  // For AI responses
  tokens?: { input: number; output: number };
  model?: string;
  
  // For tool executions
  toolName?: string;
  args?: any;
  
  // For file operations
  filePath?: string;
  fileSize?: number;
}

interface SlowOperation {
  event: TimedEvent;
  rank: number;
  suggestion?: string;
}

interface OptimizationSuggestion {
  id: string;
  type: 'model' | 'batching' | 'prompting' | 'context';
  title: string;
  description: string;
  estimatedSaving: string;  // e.g., "-40% time"
  affectedEvents: string[];  // Event IDs
}

// Flame graph data structure
interface FlameNode {
  id: string;
  name: string;
  value: number;  // Duration in ms
  children: FlameNode[];
  
  // For rendering
  x: number;
  y: number;
  width: number;
  color: string;
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Performance where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)

type PerformanceState =
  { data :: Maybe PerformanceData
  , selectedEvent :: Maybe TimedEvent
  , flameGraphZoom :: FlameZoom
  , activeTab :: PerformanceTab
  }

data PerformanceTab
  = OverviewTab
  | TokensTab
  | TimelineTab
  | SuggestionsTab

type FlameZoom =
  { startTime :: Number
  , endTime :: Number
  , depth :: Int
  }

data Action
  = Initialize
  | LoadData String  -- session ID
  | DataLoaded PerformanceData
  | SelectEvent TimedEvent
  | ClearSelection
  | ZoomFlameGraph FlameZoom
  | ResetZoom
  | SetTab PerformanceTab
  | ApplySuggestion String
```

### Flame Graph Rendering

```purescript
module Sidepanel.Components.Performance.FlameGraph where

-- Build flame graph data from events
buildFlameGraph :: Array TimedEvent -> FlameNode
buildFlameGraph events =
  let 
    rootDuration = sumDurations events
  in
    { id: "root"
    , name: "Session"
    , value: rootDuration
    , children: map eventToNode events
    , x: 0.0
    , y: 0.0
    , width: 100.0
    , color: colorForType "session"
    }

eventToNode :: TimedEvent -> FlameNode
eventToNode event =
  { id: event.id
  , name: event.name
  , value: event.duration
  , children: map eventToNode event.children
  , x: 0.0  -- Calculated during layout
  , y: 0.0
  , width: 0.0
  , color: colorForType event.type
  }

-- Render flame graph as SVG
renderFlameGraph :: forall m. FlameNode -> FlameZoom -> H.ComponentHTML Action () m
renderFlameGraph root zoom =
  HH.div
    [ HP.class_ (H.ClassName "flame-graph-container") ]
    [ HH.svg
        [ HP.class_ (H.ClassName "flame-graph")
        , HP.attr (H.AttrName "viewBox") "0 0 1000 400"
        ]
        [ renderFlameNodes root 0 zoom ]
    , renderLegend
    , renderTooltip
    ]

renderFlameNodes :: forall m. FlameNode -> Int -> FlameZoom -> H.ComponentHTML Action () m
renderFlameNodes node depth zoom =
  let 
    -- Calculate position based on zoom
    x = calculateX node zoom
    width = calculateWidth node zoom
    y = toNumber depth * 24.0
    height = 22.0
    
    -- Skip if outside view
    visible = x + width > 0.0 && x < 1000.0
  in
    when visible $
      HH.g_
        [ -- This node's rect
          HH.rect
            [ HP.attr (H.AttrName "x") (show x)
            , HP.attr (H.AttrName "y") (show y)
            , HP.attr (H.AttrName "width") (show (max 1.0 width))
            , HP.attr (H.AttrName "height") (show height)
            , HP.attr (H.AttrName "fill") node.color
            , HP.attr (H.AttrName "stroke") "#1a1a1a"
            , HP.class_ (H.ClassName "flame-node")
            , HE.onClick \_ -> SelectEvent (nodeToEvent node)
            , HE.onDoubleClick \_ -> ZoomFlameGraph (zoomToNode node)
            ]
          
        -- Label (if wide enough)
        , when (width > 40.0) $
            HH.text_
              [ HP.attr (H.AttrName "x") (show (x + 4.0))
              , HP.attr (H.AttrName "y") (show (y + 15.0))
              , HP.class_ (H.ClassName "flame-label")
              ]
              [ HH.text $ truncateLabel node.name (width / 7.0) ]
        
        -- Children
        , HH.g_ (map (\child -> renderFlameNodes child (depth + 1) zoom) node.children)
        ]

colorForType :: String -> String
colorForType = case _ of
  "session" -> "#3b82f6"
  "ai_response" -> "#8b5cf6"
  "tool_execution" -> "#f59e0b"
  "file_read" -> "#22c55e"
  "file_write" -> "#ef4444"
  "network_request" -> "#06b6d4"
  _ -> "#71717a"
```

---

## CSS Styling

```css
.performance-view {
  display: flex;
  flex-direction: column;
  height: 100%;
  overflow: hidden;
}

.performance-summary {
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  gap: var(--space-3);
  padding: var(--space-4);
  background: var(--color-bg-surface);
  border-bottom: 1px solid var(--color-border-subtle);
}

.summary-stat {
  text-align: center;
}

.summary-stat__value {
  font-family: var(--font-mono);
  font-size: var(--font-size-2xl);
  font-weight: var(--font-weight-bold);
  color: var(--color-text-primary);
}

.summary-stat__label {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  text-transform: uppercase;
}

.time-breakdown {
  padding: var(--space-4);
}

.breakdown-bar {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  margin-bottom: var(--space-2);
}

.breakdown-bar__track {
  flex: 1;
  height: 16px;
  background: var(--color-bg-base);
  border-radius: 8px;
  overflow: hidden;
}

.breakdown-bar__fill {
  height: 100%;
  transition: width var(--transition-base);
}

.breakdown-bar__fill--ai {
  background: var(--color-diem);
}

.breakdown-bar__fill--tools {
  background: var(--color-warning);
}

.breakdown-bar__fill--network {
  background: var(--color-info);
}

.flame-graph-container {
  flex: 1;
  overflow: hidden;
  padding: var(--space-4);
}

.flame-graph {
  width: 100%;
  height: 100%;
}

.flame-node {
  cursor: pointer;
  transition: opacity var(--transition-fast);
}

.flame-node:hover {
  opacity: 0.8;
}

.flame-label {
  font-family: var(--font-mono);
  font-size: 11px;
  fill: white;
  pointer-events: none;
}

.slowest-operations {
  padding: var(--space-4);
}

.slow-operation {
  display: flex;
  gap: var(--space-3);
  padding: var(--space-3);
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  margin-bottom: var(--space-2);
}

.slow-operation__rank {
  width: 24px;
  height: 24px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--color-warning-dim);
  color: var(--color-warning);
  border-radius: 50%;
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-bold);
}

.slow-operation__content {
  flex: 1;
}

.slow-operation__title {
  font-family: var(--font-mono);
  font-weight: var(--font-weight-medium);
}

.slow-operation__duration {
  font-family: var(--font-mono);
  color: var(--color-error);
}

.slow-operation__suggestion {
  display: flex;
  align-items: flex-start;
  gap: var(--space-2);
  margin-top: var(--space-2);
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.optimization-suggestions {
  padding: var(--space-4);
}

.suggestion-card {
  display: flex;
  align-items: flex-start;
  gap: var(--space-3);
  padding: var(--space-3);
  background: var(--color-bg-surface);
  border: 1px solid var(--color-primary-dim);
  border-left: 3px solid var(--color-primary);
  border-radius: 8px;
  margin-bottom: var(--space-2);
}

.suggestion-card__icon {
  font-size: 20px;
}

.suggestion-card__title {
  font-weight: var(--font-weight-medium);
  color: var(--color-text-primary);
}

.suggestion-card__description {
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
  margin-top: var(--space-1);
}

.suggestion-card__saving {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-success);
  margin-top: var(--space-2);
}
```

---

## Performance Data Collection

```typescript
// bridge/src/performance/collector.ts

export class PerformanceCollector {
  private events: TimedEvent[] = [];
  private eventStack: TimedEvent[] = [];
  
  startSession(sessionId: string): void {
    this.events = [];
    this.eventStack = [];
    
    const rootEvent: TimedEvent = {
      id: sessionId,
      type: 'session',
      name: 'Session',
      startTime: Date.now(),
      endTime: 0,
      duration: 0,
      children: [],
      metadata: {}
    };
    
    this.eventStack.push(rootEvent);
  }
  
  startEvent(type: EventType, name: string, metadata: EventMetadata = {}): string {
    const event: TimedEvent = {
      id: generateId(),
      type,
      name,
      startTime: Date.now(),
      endTime: 0,
      duration: 0,
      children: [],
      metadata
    };
    
    // Add as child of current parent
    const parent = this.eventStack[this.eventStack.length - 1];
    parent.children.push(event);
    
    // Push onto stack
    this.eventStack.push(event);
    
    return event.id;
  }
  
  endEvent(eventId: string): void {
    const event = this.eventStack.pop();
    if (event?.id !== eventId) {
      console.warn('Event end mismatch');
      return;
    }
    
    event.endTime = Date.now();
    event.duration = event.endTime - event.startTime;
  }
  
  getPerformanceData(): PerformanceData {
    const root = this.eventStack[0];
    root.endTime = Date.now();
    root.duration = root.endTime - root.startTime;
    
    return {
      sessionId: root.id,
      totalDuration: root.duration,
      aiThinkingTime: this.sumByType('ai_response'),
      toolExecutionTime: this.sumByType('tool_execution'),
      networkTime: this.sumByType('network_request'),
      totalTokens: this.sumTokens(),
      totalCost: this.sumCost(),
      messageCount: this.countByType('ai_response'),
      toolCallCount: this.countByType('tool_execution'),
      events: root.children,
      slowestOperations: this.findSlowest(5),
      suggestions: this.generateSuggestions()
    };
  }
  
  private generateSuggestions(): OptimizationSuggestion[] {
    const suggestions: OptimizationSuggestion[] = [];
    
    // Check for sequential file reads that could be batched
    const sequentialReads = this.findSequentialReads();
    if (sequentialReads.length > 2) {
      suggestions.push({
        id: 'batch-reads',
        type: 'batching',
        title: 'Batch file reads',
        description: `${sequentialReads.length} sequential reads could be batched`,
        estimatedSaving: '-15% time est.',
        affectedEvents: sequentialReads.map(e => e.id)
      });
    }
    
    // Check for large outputs that could be split
    const largeOutputs = this.findLargeOutputs(3000);
    if (largeOutputs.length > 0) {
      suggestions.push({
        id: 'split-outputs',
        type: 'prompting',
        title: 'Request incremental outputs',
        description: `${largeOutputs.length} responses had >3000 tokens. Ask for incremental delivery.`,
        estimatedSaving: '-20% time est.',
        affectedEvents: largeOutputs.map(e => e.id)
      });
    }
    
    return suggestions;
  }
}
```

---

## Related Specifications

- `13-TOKEN-USAGE-METRICS.md` - Token tracking
- `54-SESSION-PANEL.md` - Session details
- `65-SESSION-RECORDING.md` - Session timeline

---

*"What gets measured gets optimized."*
