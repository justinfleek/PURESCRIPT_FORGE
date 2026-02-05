# 66-SEARCH-VIEW: Universal Search

## Overview

Universal Search provides instant access to everything: sessions, messages, files, proofs, recordings, and settings. It's the command center for finding anything in your AI coding history.

---

## Design Principles

1. **Instant** - Results appear as you type
2. **Universal** - Search everything from one place
3. **Contextual** - Results grouped by type with previews
4. **Actionable** - Jump directly to any result
5. **Keyboard-first** - Full navigation without mouse

---

## Visual Design

### Search Modal

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                        [✕]  │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │  🔍  authentication token expiration                                   │ │
│  └───────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ FILTERS ─────────────────────────────────────────────────────────────┐ │
│  │  Type: [All ▼]   Date: [Any Time ▼]   Model: [Any ▼]   In: [All ▼]   │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Found 47 results for "authentication token expiration"                    │
│                                                                             │
│  ┌─ SESSIONS (5) ────────────────────────────────────────── [See All →] ─┐ │
│  │                                                                        │ │
│  │  ● Debug Auth Session                                     Jan 15      │ │
│  │    "...fix the token expiration check that was causing..."            │ │
│  │                                                                        │ │
│  │  ● Auth Middleware Refactor                               Jan 10      │ │
│  │    "...proper token expiration handling with refresh..."              │ │
│  │                                                                        │ │
│  │  ○ Session Management Deep Dive                           Jan 8       │ │
│  │    "...authentication tokens and their expiration..."                 │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ MESSAGES (28) ───────────────────────────────────────── [See All →] ─┐ │
│  │                                                                        │ │
│  │  🤖 "The token expiration check is using local time instead of..."    │ │
│  │     Debug Auth • Jan 15 • 12:31 PM                       [Jump →]     │ │
│  │                                                                        │ │
│  │  👤 "How do I handle token expiration gracefully without..."          │ │
│  │     Auth Refactor • Jan 10 • 3:45 PM                     [Jump →]     │ │
│  │                                                                        │ │
│  │  🤖 "Here's a robust approach to token expiration that..."            │ │
│  │     Auth Refactor • Jan 10 • 3:46 PM                     [Jump →]     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ FILES (8) ───────────────────────────────────────────── [See All →] ─┐ │
│  │                                                                        │ │
│  │  📄 src/auth/session.ts                                               │ │
│  │     Line 42: return expiry.getTime() > Date.now();       [Open →]     │ │
│  │                                                                        │ │
│  │  📄 src/auth/middleware.ts                                            │ │
│  │     Line 15: const TOKEN_EXPIRATION = 3600;              [Open →]     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ PROOFS (3) ──────────────────────────────────────────── [See All →] ─┐ │
│  │                                                                        │ │
│  │  🔬 theorem token_expiration_valid                                    │ │
│  │     AuthInvariant.lean • Proved                          [View →]     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ RECORDINGS (3) ──────────────────────────────────────── [See All →] ─┐ │
│  │                                                                        │ │
│  │  🎬 Auth Bug Fix Session                                              │ │
│  │     47 min • Jan 15                                      [Play →]     │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ↑↓ Navigate   ⏎ Open   ⌘⏎ Open in new tab   Esc Close                   │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Expanded Results View

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SEARCH: "authentication" in Messages                              [✕]     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ FILTERS ─────────────────────────────────────────────────────────────┐ │
│  │  Role: [All ▼]   Has Code: [Any ▼]   Has Tool: [Any ▼]               │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  28 messages matching "authentication"                                     │
│                                                                             │
│  ┌────────────────────────────────────────────────────────────────────────┐│
│  │                                                                        ││
│  │  🤖 Assistant • Debug Auth • Jan 15, 12:31 PM                         ││
│  │                                                                        ││
│  │  The token expiration check is using local time instead of UTC.       ││
│  │  This is why users in different timezones experience random           ││
│  │  logouts. The `authentication` middleware compares...                 ││
│  │                                                                        ││
│  │  ```typescript                                                        ││
│  │  // Before (buggy)                                                    ││
│  │  return expiry.getTime() > new Date().getTime();                      ││
│  │                                                                        ││
│  │  // After (fixed)                                                     ││
│  │  return expiry.getTime() > Date.now();                                ││
│  │  ```                                                                  ││
│  │                                                                        ││
│  │  [Go to Session] [Copy] [Share]                                       ││
│  │                                                                        ││
│  └────────────────────────────────────────────────────────────────────────┘│
│                                                                             │
│  ┌────────────────────────────────────────────────────────────────────────┐│
│  │                                                                        ││
│  │  👤 User • Auth Refactor • Jan 10, 3:45 PM                            ││
│  │                                                                        ││
│  │  How do I handle token authentication expiration gracefully           ││
│  │  without forcing users to re-login?                                   ││
│  │                                                                        ││
│  │  [Go to Session] [Copy]                                               ││
│  │                                                                        ││
│  └────────────────────────────────────────────────────────────────────────┘│
│                                                                             │
│  [Load More Results...]                                                    │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Search Capabilities

### Searchable Content

| Type | Indexed Fields | Example Queries |
|------|----------------|-----------------|
| Sessions | title, description, tags | "auth bug", "#debugging" |
| Messages | content, role, tool names | "useEffect", "@assistant", "read_file" |
| Files | path, content snippets, language | "session.ts", "typescript", "async function" |
| Proofs | theorem names, file, status | "token_valid", "proved", "2 goals" |
| Recordings | title, description, tags | "tutorial", "#react" |
| Diffs | file path, change description | "line 42", "timezone fix" |

### Query Syntax

```
# Basic search
authentication token

# Exact phrase
"token expiration"

# Field-specific
role:assistant content:useEffect
type:session title:debug

# Boolean operators
authentication AND token
auth OR authentication
authentication NOT refresh

# Date filters
date:today
date:this-week
date:2025-01-15
date:>2025-01-01

# Type filters
type:session
type:message
type:file
type:proof
type:recording

# Tag filters
#debugging
#auth
#typescript

# Negation
-type:file
-#draft
```

---

## Data Model

```typescript
interface SearchQuery {
  text: string;
  filters: SearchFilters;
}

interface SearchFilters {
  types?: SearchableType[];
  dateRange?: {
    start?: Date;
    end?: Date;
  };
  model?: string;
  tags?: string[];
  sessionId?: string;  // Search within session
}

type SearchableType = 
  | 'session' 
  | 'message' 
  | 'file' 
  | 'proof' 
  | 'recording' 
  | 'diff';

interface SearchResult {
  id: string;
  type: SearchableType;
  score: number;  // Relevance score
  
  // Display
  title: string;
  preview: string;  // Highlighted snippet
  timestamp: Date;
  
  // Navigation
  link: SearchLink;
  
  // Type-specific metadata
  metadata: Record<string, any>;
}

interface SearchLink {
  type: 'session' | 'message' | 'file' | 'proof' | 'recording';
  id: string;
  anchor?: string;  // For jumping to specific location
}

interface SearchResults {
  query: SearchQuery;
  totalCount: number;
  
  // Grouped results
  sessions: SearchResult[];
  messages: SearchResult[];
  files: SearchResult[];
  proofs: SearchResult[];
  recordings: SearchResult[];
  
  // Timing
  searchTimeMs: number;
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Search where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)

type SearchState =
  { query :: String
  , filters :: SearchFilters
  , results :: Maybe SearchResults
  , isSearching :: Boolean
  , selectedIndex :: Int
  , expandedType :: Maybe SearchableType
  }

type SearchFilters =
  { types :: Array SearchableType
  , dateRange :: Maybe DateRange
  , model :: Maybe String
  , tags :: Array String
  }

data SearchableType
  = SessionType
  | MessageType
  | FileType
  | ProofType
  | RecordingType

type SearchResult =
  { id :: String
  , resultType :: SearchableType
  , score :: Number
  , title :: String
  , preview :: String
  , timestamp :: DateTime
  , metadata :: Foreign
  }

data Action
  = SetQuery String
  | SetFilter SearchFilters
  | Search
  | SearchComplete SearchResults
  | SelectResult Int
  | OpenResult SearchResult
  | ExpandType SearchableType
  | CollapseType
  | NavigateUp
  | NavigateDown
  | Close
```

### Search Component

```purescript
component :: forall q m. MonadAff m => H.Component q Unit Output m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: SearchState
initialState =
  { query: ""
  , filters: defaultFilters
  , results: Nothing
  , isSearching: false
  , selectedIndex: 0
  , expandedType: Nothing
  }

render :: forall m. SearchState -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "search-modal")
    , HP.tabIndex 0
    , HE.onKeyDown handleKeyDown
    ]
    [ -- Search input
      renderSearchInput state
    
    -- Filters
    , renderFilters state.filters
    
    -- Results
    , case state.results of
        Nothing ->
          if state.query == ""
            then renderEmptyState
            else HH.text ""
        Just results ->
          if state.isSearching
            then renderLoading
            else renderResults results state
    
    -- Keyboard hints
    , renderKeyboardHints
    ]

renderSearchInput :: forall m. SearchState -> H.ComponentHTML Action () m
renderSearchInput state =
  HH.div
    [ HP.class_ (H.ClassName "search-input-container") ]
    [ HH.span [ HP.class_ (H.ClassName "search-icon") ] [ HH.text "🔍" ]
    , HH.input
        [ HP.class_ (H.ClassName "search-input")
        , HP.placeholder "Search sessions, messages, files, proofs..."
        , HP.value state.query
        , HP.autofocus true
        , HE.onValueInput SetQuery
        ]
    ]

renderResults :: forall m. SearchResults -> SearchState -> H.ComponentHTML Action () m
renderResults results state =
  HH.div
    [ HP.class_ (H.ClassName "search-results") ]
    [ HH.div
        [ HP.class_ (H.ClassName "search-results__summary") ]
        [ HH.text $ "Found " <> show results.totalCount <> " results" ]
    
    -- Sessions
    , when (not $ null results.sessions) $
        renderResultGroup "Sessions" SessionType results.sessions state
    
    -- Messages
    , when (not $ null results.messages) $
        renderResultGroup "Messages" MessageType results.messages state
    
    -- Files
    , when (not $ null results.files) $
        renderResultGroup "Files" FileType results.files state
    
    -- Proofs
    , when (not $ null results.proofs) $
        renderResultGroup "Proofs" ProofType results.proofs state
    
    -- Recordings
    , when (not $ null results.recordings) $
        renderResultGroup "Recordings" RecordingType results.recordings state
    ]

renderResultGroup :: forall m. String -> SearchableType -> Array SearchResult -> SearchState -> H.ComponentHTML Action () m
renderResultGroup title resultType results state =
  let 
    isExpanded = state.expandedType == Just resultType
    displayResults = if isExpanded then results else take 3 results
  in
    HH.div
      [ HP.class_ (H.ClassName "result-group") ]
      [ HH.div
          [ HP.class_ (H.ClassName "result-group__header") ]
          [ HH.span_ [ HH.text $ title <> " (" <> show (length results) <> ")" ]
          , when (length results > 3) $
              HH.button
                [ HP.class_ (H.ClassName "result-group__expand")
                , HE.onClick \_ -> if isExpanded then CollapseType else ExpandType resultType
                ]
                [ HH.text $ if isExpanded then "Show Less" else "See All →" ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "result-group__items") ]
          (mapWithIndex (renderResultItem state.selectedIndex) displayResults)
      ]

renderResultItem :: forall m. Int -> Int -> SearchResult -> H.ComponentHTML Action () m
renderResultItem selectedIndex index result =
  let isSelected = selectedIndex == index
  in
    HH.div
      [ HP.classes $ resultItemClasses isSelected
      , HE.onClick \_ -> OpenResult result
      ]
      [ HH.span [ HP.class_ (H.ClassName "result-item__icon") ]
          [ HH.text $ typeIcon result.resultType ]
      , HH.div
          [ HP.class_ (H.ClassName "result-item__content") ]
          [ HH.div [ HP.class_ (H.ClassName "result-item__title") ]
              [ HH.text result.title ]
          , HH.div [ HP.class_ (H.ClassName "result-item__preview") ]
              -- Render with highlighting
              [ renderHighlightedText result.preview ]
          ]
      , HH.span [ HP.class_ (H.ClassName "result-item__date") ]
          [ HH.text $ formatRelativeDate result.timestamp ]
      ]

typeIcon :: SearchableType -> String
typeIcon = case _ of
  SessionType -> "●"
  MessageType -> "💬"
  FileType -> "📄"
  ProofType -> "🔬"
  RecordingType -> "🎬"
```

### Keyboard Navigation

```purescript
handleKeyDown :: KeyboardEvent -> Maybe Action
handleKeyDown event =
  case key event of
    "ArrowUp" -> Just NavigateUp
    "ArrowDown" -> Just NavigateDown
    "Enter" -> Just (OpenSelected)
    "Escape" -> Just Close
    _ -> Nothing

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  SetQuery query -> do
    H.modify_ _ { query = query }
    -- Debounce search
    when (String.length query >= 2) do
      H.liftAff $ delay (Milliseconds 150.0)
      currentQuery <- H.gets _.query
      when (currentQuery == query) do
        handleAction Search
  
  Search -> do
    state <- H.get
    H.modify_ _ { isSearching = true }
    
    results <- H.liftAff $ performSearch state.query state.filters
    
    H.modify_ _ { results = Just results, isSearching = false, selectedIndex = 0 }
  
  NavigateUp -> do
    H.modify_ \s -> s { selectedIndex = max 0 (s.selectedIndex - 1) }
  
  NavigateDown -> do
    total <- H.gets (maybe 0 totalResults <<< _.results)
    H.modify_ \s -> s { selectedIndex = min (total - 1) (s.selectedIndex + 1) }
  
  OpenResult result -> do
    H.raise (NavigateTo result.link)
    handleAction Close
  
  _ -> pure unit
```

---

## Search Backend

### Indexing

```typescript
// bridge/src/search/indexer.ts
import MiniSearch from 'minisearch';

export class SearchIndexer {
  private sessionIndex: MiniSearch;
  private messageIndex: MiniSearch;
  private fileIndex: MiniSearch;
  
  constructor() {
    this.sessionIndex = new MiniSearch({
      fields: ['title', 'description', 'tags'],
      storeFields: ['id', 'title', 'timestamp']
    });
    
    this.messageIndex = new MiniSearch({
      fields: ['content', 'role'],
      storeFields: ['id', 'sessionId', 'role', 'timestamp']
    });
    
    this.fileIndex = new MiniSearch({
      fields: ['path', 'content'],
      storeFields: ['id', 'path', 'language']
    });
  }
  
  indexSession(session: Session): void {
    this.sessionIndex.add({
      id: session.id,
      title: session.title,
      description: session.description ?? '',
      tags: session.tags?.join(' ') ?? '',
      timestamp: session.createdAt
    });
  }
  
  indexMessage(message: Message, sessionId: string): void {
    this.messageIndex.add({
      id: message.id,
      sessionId,
      content: message.content,
      role: message.role,
      timestamp: message.timestamp
    });
  }
  
  search(query: string, filters: SearchFilters): SearchResults {
    const results: SearchResults = {
      query: { text: query, filters },
      totalCount: 0,
      sessions: [],
      messages: [],
      files: [],
      proofs: [],
      recordings: [],
      searchTimeMs: 0
    };
    
    const startTime = performance.now();
    
    // Search each index
    if (filters.types?.includes('session') ?? true) {
      results.sessions = this.searchSessions(query, filters);
    }
    
    if (filters.types?.includes('message') ?? true) {
      results.messages = this.searchMessages(query, filters);
    }
    
    if (filters.types?.includes('file') ?? true) {
      results.files = this.searchFiles(query, filters);
    }
    
    results.totalCount = 
      results.sessions.length +
      results.messages.length +
      results.files.length +
      results.proofs.length +
      results.recordings.length;
    
    results.searchTimeMs = performance.now() - startTime;
    
    return results;
  }
  
  private searchSessions(query: string, filters: SearchFilters): SearchResult[] {
    const rawResults = this.sessionIndex.search(query, { prefix: true, fuzzy: 0.2 });
    
    return rawResults
      .filter(r => this.matchesFilters(r, filters))
      .map(r => ({
        id: r.id,
        type: 'session' as const,
        score: r.score,
        title: r.title,
        preview: this.highlightMatches(r.description, query),
        timestamp: r.timestamp,
        metadata: {},
        link: { type: 'session', id: r.id }
      }));
  }
}
```

---

## Related Specifications

- `23-SESSION-MANAGEMENT.md` - Session data
- `65-SESSION-RECORDING.md` - Recording search
- `48-KEYBOARD-NAVIGATION.md` - Keyboard patterns

---

*"Find anything instantly. Navigate everywhere effortlessly."*
