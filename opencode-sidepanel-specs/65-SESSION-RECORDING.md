# 65-SESSION-RECORDING: Record and Playback System

## Overview

Session Recording captures every event in an AI coding session for later playback, sharing, and analysis. Think of it as "screen recording for AI conversations" but with full interactivity.

---

## Use Cases

1. **Onboarding** - Show new team members how to use AI effectively
2. **Debugging** - "Watch" what happened when something went wrong
3. **Learning** - Study how experts prompt and iterate
4. **Documentation** - Record how features were built
5. **Sharing** - Export recordings for blog posts, tutorials

---

## Visual Design

### Recordings Library

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  RECORDINGS                                     [+ Start Recording] [Import]│
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ FILTERS ─────────────────────────────────────────────────────────────┐ │
│  │  Search: [                    ]   Date: [Any ▼]   Tag: [All ▼]        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ RECORDINGS ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌────────────────────────────────────────────────────────────────┐   │ │
│  │  │  🎬  Auth Bug Fix Session                              ★ ★ ★   │   │ │
│  │  │                                                                 │   │ │
│  │  │  Jan 15, 2025 • 47 minutes • 23,955 tokens • $0.014            │   │ │
│  │  │  Tags: #debugging #auth #typescript                             │   │ │
│  │  │                                                                 │   │ │
│  │  │  Fixed timezone bug in token expiration. Includes test          │   │ │
│  │  │  creation and proof verification.                               │   │ │
│  │  │                                                                 │   │ │
│  │  │  [▶ Play]  [Export]  [Share]  [Edit]  [Delete]                 │   │ │
│  │  └────────────────────────────────────────────────────────────────┘   │ │
│  │                                                                        │ │
│  │  ┌────────────────────────────────────────────────────────────────┐   │ │
│  │  │  🎬  React Component Refactor                          ★ ★     │   │ │
│  │  │                                                                 │   │ │
│  │  │  Jan 14, 2025 • 1h 23m • 67,234 tokens • $0.041                │   │ │
│  │  │  Tags: #react #refactoring                                      │   │ │
│  │  │                                                                 │   │ │
│  │  │  Major refactoring of Auth component to use hooks pattern.     │   │ │
│  │  │                                                                 │   │ │
│  │  │  [▶ Play]  [Export]  [Share]  [Edit]  [Delete]                 │   │ │
│  │  └────────────────────────────────────────────────────────────────┘   │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Showing 2 of 15 recordings                              [Load More]        │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Playback Interface

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  NOW PLAYING: Auth Bug Fix Session                         [✕ Close Player]│
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ PLAYBACK AREA ───────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │ │
│  │  │                                                                  │  │ │
│  │  │   👤 12:30 PM                                                    │  │ │
│  │  │   Help me debug this authentication flow. Users are getting      │  │ │
│  │  │   logged out randomly.                                           │  │ │
│  │  │                                                                  │  │ │
│  │  │   🤖 12:30 PM  ████████████░░░░░░░░░░░░░░  Typing...            │  │ │
│  │  │   I'll analyze the authentication code. Let me start by         │  │ │
│  │  │   reading the relevant files.                                    │  │ │
│  │  │                                                                  │  │ │
│  │  └─────────────────────────────────────────────────────────────────┘  │ │
│  │                                                                        │ │
│  │  ┌─ SIDEBAR STATE ──────────────────────────────────────────────────┐ │ │
│  │  │  Diem: 48.2    Tokens: 1,801    Files: 2                        │ │ │
│  │  └──────────────────────────────────────────────────────────────────┘ │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ CONTROLS ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │   ◄◄    ▶    ►►   │████████░░░░░░░░░░░░░░░│   12:31 / 47:00         │ │
│  │                                                                        │ │
│  │   Speed: [0.5x] [1x] [2x] [4x]           🔊 ────●───── 100%          │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ TIMELINE ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  │ 👤 │ 🤖 │ 📄 │ 🤖 │ 📝 │ 👤 │ 🤖 │ ✓ │ 👤 │ 🤖 │               │ │
│  │  │msg │resp│read│resp│write│msg │resp│proof│msg │resp│               │ │
│  │  └────┴────┴────┴────┴─────┴────┴────┴─────┴────┴────┘               │ │
│  │   ▲                                                                    │ │
│  │   Current position                                                     │ │
│  │                                                                        │ │
│  │  [Jump to: Message ▼]  [Jump to: Tool ▼]  [Jump to: Marker ▼]        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  [Add Marker]  [Add Comment]  [Export Clip]  [Share]                       │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

### Recording Structure

```typescript
interface Recording {
  id: string;
  title: string;
  description: string;
  
  // Metadata
  createdAt: Date;
  duration: number;  // milliseconds
  totalTokens: number;
  totalCost: number;
  tags: string[];
  rating: number;  // 1-5 stars
  
  // The actual data
  events: RecordedEvent[];
  snapshots: StateSnapshot[];  // Periodic full state for seeking
  
  // User additions
  markers: Marker[];
  comments: Comment[];
  
  // Export info
  exportedAt?: Date;
  shareUrl?: string;
}

interface RecordedEvent {
  id: string;
  timestamp: number;  // ms from start
  type: EventType;
  data: any;  // Event-specific payload
}

type EventType =
  | 'message.user'
  | 'message.assistant.start'
  | 'message.assistant.chunk'
  | 'message.assistant.complete'
  | 'tool.start'
  | 'tool.complete'
  | 'file.read'
  | 'file.write'
  | 'balance.update'
  | 'proof.update'
  | 'error';

interface StateSnapshot {
  timestamp: number;
  state: {
    balance: BalanceState;
    session: SessionState;
    context: ContextEntry[];
    proof: ProofState;
  };
}

interface Marker {
  id: string;
  timestamp: number;
  label: string;
  color: string;
}

interface Comment {
  id: string;
  timestamp: number;
  text: string;
  author: string;
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Recording where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)

type Recording =
  { id :: String
  , title :: String
  , description :: String
  , createdAt :: DateTime
  , duration :: Int  -- ms
  , totalTokens :: Int
  , totalCost :: Number
  , tags :: Array String
  , rating :: Int
  }

data PlaybackState
  = Stopped
  | Playing
  | Paused

type PlayerState =
  { recording :: Maybe Recording
  , playbackState :: PlaybackState
  , currentTime :: Int  -- ms from start
  , playbackSpeed :: Number  -- 0.5, 1, 2, 4
  , volume :: Number  -- 0-1
  
  -- Current frame state (what to display)
  , currentFrame :: Maybe FrameState
  
  -- Navigation
  , events :: Array RecordedEvent
  , markers :: Array Marker
  }

type FrameState =
  { messages :: Array Message
  , balance :: BalanceState
  , tokens :: Int
  , filesInContext :: Array String
  , proofGoals :: Int
  }

data Action
  = LoadRecording String
  | RecordingLoaded Recording
  | Play
  | Pause
  | Stop
  | Seek Int  -- timestamp
  | SetSpeed Number
  | SetVolume Number
  | JumpToEvent String
  | JumpToMarker String
  | AddMarker String
  | AddComment String
  | Export
  | Share
```

### Playback Engine

```purescript
module Sidepanel.Recording.PlaybackEngine where

-- Core playback loop
startPlayback :: forall m. MonadAff m => PlayerState -> m Unit
startPlayback state = do
  -- Fork playback fiber
  fiber <- H.fork $ playbackLoop state.currentTime state.playbackSpeed
  
  -- Store fiber reference for pause/stop
  H.modify_ _ { playbackFiber = Just fiber }

playbackLoop :: forall m. MonadAff m => Int -> Number -> m Unit
playbackLoop currentTime speed = do
  state <- H.get
  
  case state.playbackState of
    Playing -> do
      -- Calculate next frame time
      let realTimeElapsed = 16  -- ~60fps
      let recordingTimeElapsed = round (toNumber realTimeElapsed * speed)
      let nextTime = currentTime + recordingTimeElapsed
      
      -- Find and apply events up to nextTime
      let eventsToApply = getEventsBetween currentTime nextTime state.events
      for_ eventsToApply applyEvent
      
      -- Update current time
      H.modify_ _ { currentTime = nextTime }
      
      -- Check if at end
      if nextTime >= state.recording.duration
        then H.modify_ _ { playbackState = Stopped }
        else do
          H.liftAff $ delay (Milliseconds 16.0)
          playbackLoop nextTime speed
    
    _ -> pure unit  -- Stopped or paused

applyEvent :: forall m. MonadAff m => RecordedEvent -> m Unit
applyEvent event = case event.type of
  "message.user" -> do
    H.modify_ \s -> s { currentFrame = addUserMessage event.data s.currentFrame }
  
  "message.assistant.chunk" -> do
    H.modify_ \s -> s { currentFrame = appendAssistantChunk event.data s.currentFrame }
  
  "message.assistant.complete" -> do
    H.modify_ \s -> s { currentFrame = completeAssistantMessage event.data s.currentFrame }
  
  "tool.start" -> do
    H.modify_ \s -> s { currentFrame = showToolStart event.data s.currentFrame }
  
  "tool.complete" -> do
    H.modify_ \s -> s { currentFrame = showToolComplete event.data s.currentFrame }
  
  "balance.update" -> do
    H.modify_ \s -> s { currentFrame = updateBalance event.data s.currentFrame }
  
  _ -> pure unit

-- Seeking uses snapshots for efficiency
seekTo :: forall m. MonadAff m => Int -> m Unit
seekTo timestamp = do
  state <- H.get
  
  -- Find nearest snapshot before timestamp
  let snapshot = findNearestSnapshot timestamp state.snapshots
  
  -- Apply snapshot state
  H.modify_ _ { currentFrame = snapshotToFrame snapshot }
  
  -- Apply events from snapshot to target
  let eventsToApply = getEventsBetween snapshot.timestamp timestamp state.events
  for_ eventsToApply applyEvent
  
  H.modify_ _ { currentTime = timestamp }
```

---

## Recording Capture

### Bridge-Side Recording

```typescript
// bridge/src/recording/recorder.ts

export class SessionRecorder {
  private recording: Recording | null = null;
  private events: RecordedEvent[] = [];
  private startTime: number = 0;
  private snapshotInterval: NodeJS.Timer | null = null;
  
  startRecording(title: string): void {
    this.recording = {
      id: generateId(),
      title,
      description: '',
      createdAt: new Date(),
      duration: 0,
      totalTokens: 0,
      totalCost: 0,
      tags: [],
      rating: 0,
      events: [],
      snapshots: [],
      markers: [],
      comments: []
    };
    
    this.events = [];
    this.startTime = Date.now();
    
    // Capture initial state snapshot
    this.captureSnapshot();
    
    // Snapshot every 30 seconds for efficient seeking
    this.snapshotInterval = setInterval(() => {
      this.captureSnapshot();
    }, 30000);
    
    // Subscribe to all events
    this.subscribeToEvents();
  }
  
  stopRecording(): Recording {
    if (this.snapshotInterval) {
      clearInterval(this.snapshotInterval);
    }
    
    this.recording!.duration = Date.now() - this.startTime;
    this.recording!.events = this.events;
    
    // Calculate totals
    this.recording!.totalTokens = this.calculateTotalTokens();
    this.recording!.totalCost = this.calculateTotalCost();
    
    // Save to storage
    this.saveRecording(this.recording!);
    
    return this.recording!;
  }
  
  private subscribeToEvents(): void {
    // Message events
    openCodeClient.on('message.created', (msg) => {
      if (msg.role === 'user') {
        this.recordEvent('message.user', msg);
      }
    });
    
    openCodeClient.on('stream.chunk', (chunk) => {
      this.recordEvent('message.assistant.chunk', chunk);
    });
    
    openCodeClient.on('message.completed', (msg) => {
      this.recordEvent('message.assistant.complete', msg);
    });
    
    // Tool events
    openCodeClient.on('tool.execute.before', (tool) => {
      this.recordEvent('tool.start', tool);
    });
    
    openCodeClient.on('tool.execute.after', (tool, result, duration) => {
      this.recordEvent('tool.complete', { tool, result, duration });
    });
    
    // State events
    store.on('balance.update', (balance) => {
      this.recordEvent('balance.update', balance);
    });
    
    store.on('proof.update', (proof) => {
      this.recordEvent('proof.update', proof);
    });
  }
  
  private recordEvent(type: EventType, data: any): void {
    this.events.push({
      id: generateId(),
      timestamp: Date.now() - this.startTime,
      type,
      data
    });
  }
  
  private captureSnapshot(): void {
    const state = store.getState();
    
    this.recording!.snapshots.push({
      timestamp: Date.now() - this.startTime,
      state: {
        balance: state.balance,
        session: state.session,
        context: contextTracker.getEntries(),
        proof: state.proof
      }
    });
  }
}
```

---

## Export Formats

### JSON Export (Full Fidelity)

```json
{
  "version": "1.0",
  "recording": {
    "id": "rec_abc123",
    "title": "Auth Bug Fix Session",
    "duration": 2820000,
    "totalTokens": 23955,
    "events": [
      {
        "timestamp": 0,
        "type": "message.user",
        "data": { "content": "Help me debug..." }
      }
    ],
    "snapshots": []
  }
}
```

### Markdown Export (Human Readable)

```markdown
# Recording: Auth Bug Fix Session

**Date:** Jan 15, 2025  
**Duration:** 47 minutes  
**Tokens:** 23,955  
**Cost:** $0.014

## Conversation

### 12:30 PM - User
Help me debug this authentication flow. Users are getting logged out randomly.

### 12:30 PM - Assistant
I'll analyze the authentication code. Let me start by reading the relevant files.

**Tool:** `read_file` → `src/auth/session.ts`

### 12:31 PM - Assistant
I found the issue. In session.ts line 42...

## Summary
- Fixed timezone bug in token expiration
- Added test coverage
- Verified with proof
```

---

## CSS Styling

```css
.recording-player {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--color-bg-base);
}

.playback-area {
  flex: 1;
  overflow: hidden;
  display: flex;
}

.playback-content {
  flex: 1;
  overflow-y: auto;
  padding: var(--space-4);
}

.playback-sidebar {
  width: 200px;
  background: var(--color-bg-surface);
  border-left: 1px solid var(--color-border-subtle);
  padding: var(--space-3);
}

.player-controls {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-3);
  background: var(--color-bg-elevated);
  border-top: 1px solid var(--color-border-subtle);
}

.player-controls__buttons {
  display: flex;
  gap: var(--space-2);
}

.player-controls__button {
  width: 36px;
  height: 36px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 50%;
  cursor: pointer;
  transition: all var(--transition-fast);
}

.player-controls__button:hover {
  background: var(--color-bg-hover);
  border-color: var(--color-primary);
}

.player-controls__button--play {
  background: var(--color-primary);
  border-color: var(--color-primary);
  color: white;
}

.player-controls__progress {
  flex: 1;
  height: 4px;
  background: var(--color-bg-base);
  border-radius: 2px;
  cursor: pointer;
  position: relative;
}

.player-controls__progress-fill {
  height: 100%;
  background: var(--color-primary);
  border-radius: 2px;
  transition: width 0.1s linear;
}

.player-controls__time {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
  font-variant-numeric: tabular-nums;
}

.timeline {
  padding: var(--space-3);
  background: var(--color-bg-surface);
  border-top: 1px solid var(--color-border-subtle);
}

.timeline__events {
  display: flex;
  gap: 2px;
  height: 32px;
}

.timeline__event {
  flex: 1;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  background: var(--color-bg-elevated);
  border-radius: 4px;
  cursor: pointer;
  transition: background var(--transition-fast);
}

.timeline__event:hover {
  background: var(--color-primary-dim);
}

.timeline__event--current {
  background: var(--color-primary);
  color: white;
}
```

---

## Related Specifications

- `23-SESSION-MANAGEMENT.md` - Session lifecycle
- `63-TIMELINE-VIEW.md` - Timeline integration
- `64-SNAPSHOT-MANAGEMENT.md` - State snapshots

---

*"The best way to learn is to watch and replay."*
