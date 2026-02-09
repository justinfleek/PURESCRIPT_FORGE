# Tmux & Emacs Features Analysis

## Overview

Analysis of tmux and emacs features that developers find essential, compared against current implementation to identify valuable gaps.

---

## Tmux Features

### ✅ Implemented

| Feature | Status | Location |
|---------|--------|----------|
| **Session Management** | ✅ Partial | `Sidepanel.State.Sessions`, `Terminal.purs` |
| **Multiple Sessions** | ✅ Yes | Tab-based session management |
| **Session Tabs** | ✅ Yes | `SessionTabs.purs` |
| **Detach/Reattach** | ⚠️ Partial | Basic terminal state persistence |

### ❌ Missing - High Priority

#### 1. **Pane Splitting & Management**
**What:** Split terminal into multiple panes (vertical/horizontal), resize, swap, close.

**Why Critical:**
- Developers constantly need multiple views (code + terminal, logs + editor, etc.)
- Essential for multitasking workflows
- One of tmux's most-used features

**Implementation Priority:** 🔴 **HIGH**

**Key Operations:**
- `Ctrl+b %` - Split vertically
- `Ctrl+b "` - Split horizontally  
- `Ctrl+b o` - Switch panes
- `Ctrl+b {` / `}` - Swap panes
- `Ctrl+b x` - Close pane
- `Ctrl+b z` - Zoom/unzoom pane
- `Ctrl+b Space` - Toggle layouts

**Current Gap:** Only single terminal view, no splitting capability.

---

#### 2. **Synchronized Panes**
**What:** Send commands to all panes simultaneously.

**Why Critical:**
- Deploy to multiple servers
- Run same command across environments
- Essential for DevOps workflows

**Implementation Priority:** 🟡 **MEDIUM**

**Key Operations:**
- `:setw synchronize-panes on` - Enable sync
- `:setw synchronize-panes off` - Disable sync

**Current Gap:** No pane synchronization.

---

#### 3. **Copy Mode & Scrollback**
**What:** Navigate scrollback buffer, copy text without mouse, search history.

**Why Critical:**
- Essential for reviewing long command outputs
- Copy-paste without mouse
- Search through terminal history

**Implementation Priority:** 🔴 **HIGH**

**Key Operations:**
- `Ctrl+b [` - Enter copy mode
- `Space` - Start selection
- `Enter` - Copy selection
- `/` - Search forward
- `?` - Search backward
- `n` / `N` - Next/previous match

**Current Gap:** Basic scrollback exists, but no copy mode or search.

---

#### 4. **Window Management**
**What:** Multiple windows within a session, window switching, window lists.

**Why Critical:**
- Organize work into logical groups
- Switch between different contexts quickly
- Better than tabs for terminal workflows

**Implementation Priority:** 🟡 **MEDIUM**

**Key Operations:**
- `Ctrl+b c` - New window
- `Ctrl+b w` - List windows
- `Ctrl+b n` / `p` - Next/previous window
- `Ctrl+b ,` - Rename window
- `Ctrl+b &` - Kill window

**Current Gap:** Only session tabs, no window concept within sessions.

---

#### 5. **Pane Layouts**
**What:** Predefined layouts (tiled, even-horizontal, even-vertical, main-horizontal, main-vertical).

**Why Critical:**
- Quick reorganization of panes
- Consistent layouts for common workflows
- Faster than manual resizing

**Implementation Priority:** 🟢 **LOW**

**Key Operations:**
- `Ctrl+b Space` - Cycle layouts
- `:select-layout tiled` - Set specific layout

**Current Gap:** No layout system.

---

#### 6. **Session Groups**
**What:** Group multiple sessions together, attach to all in group.

**Why Critical:**
- Manage related sessions together
- Useful for microservices development
- Deploy to multiple environments simultaneously

**Implementation Priority:** 🟢 **LOW**

**Current Gap:** No session grouping.

---

## Emacs Features

### ✅ Implemented

| Feature | Status | Location |
|---------|--------|----------|
| **Keyboard Navigation** | ✅ Yes | `KeyboardNavigation.purs` |
| **Vim Bindings** | ✅ Yes | Vim-style navigation |
| **Command Palette** | ✅ Yes | `Ctrl+Shift+P` |
| **Search** | ✅ Partial | Basic search exists |

### ❌ Missing - High Priority

#### 1. **Keyboard Macros**
**What:** Record sequence of keystrokes, replay with single command.

**Why Critical:**
- Automate repetitive editing tasks
- Transform code patterns consistently
- One of emacs' most powerful features

**Implementation Priority:** 🔴 **HIGH**

**Key Operations:**
- `C-x (` - Start recording macro
- `C-x )` - Stop recording
- `C-x e` - Execute last macro
- `C-u 10 C-x e` - Execute 10 times
- `C-x C-k e` - Edit macro
- `C-x C-k n` - Name macro

**Use Cases:**
- Refactor similar code blocks
- Transform data formats
- Bulk edits with pattern

**Current Gap:** No macro recording/replay system.

---

#### 2. **Register System**
**What:** Named clipboard slots (a-z, 0-9) for storing text, positions, rectangles.

**Why Critical:**
- Multiple clipboard items simultaneously
- Store positions for quick navigation
- Essential for complex editing workflows

**Implementation Priority:** 🟡 **MEDIUM**

**Key Operations:**
- `C-x r s a` - Save region to register 'a'
- `C-x r i a` - Insert register 'a'
- `C-x r Space a` - Save point to register 'a'
- `C-x r j a` - Jump to register 'a'

**Current Gap:** Only single clipboard.

---

#### 3. **Mark & Point System**
**What:** Set marks, jump between marks, operate on region between mark and point.

**Why Critical:**
- Precise region selection
- Quick navigation to marked positions
- Foundation for many editing operations

**Implementation Priority:** 🟡 **MEDIUM**

**Key Operations:**
- `C-Space` - Set mark
- `C-x C-x` - Swap mark and point
- `C-u C-Space` - Pop mark from ring
- `C-x C-Space` - Set mark and activate region

**Current Gap:** Basic selection exists, but no mark ring or mark navigation.

---

#### 4. **Rectangular Selection**
**What:** Select rectangular regions (columns), operate on columns of text.

**Why Critical:**
- Edit aligned code columns
- Transform tables
- Bulk column operations

**Implementation Priority:** 🟡 **MEDIUM**

**Key Operations:**
- `C-x r r` - Copy rectangle
- `C-x r k` - Kill rectangle
- `C-x r y` - Yank rectangle
- `C-x r o` - Open rectangle (insert spaces)
- `C-x r t` - String rectangle (replace with text)

**Current Gap:** No rectangular selection mode.

---

#### 5. **Narrowing**
**What:** Hide everything except selected region, focus editing on subset.

**Why Critical:**
- Focus on specific function/class
- Reduce visual clutter
- Essential for large file editing

**Implementation Priority:** 🟢 **LOW**

**Key Operations:**
- `C-x n n` - Narrow to region
- `C-x n w` - Widen (show all)

**Current Gap:** No narrowing capability.

---

#### 6. **Occur Mode**
**What:** Search and display all matches in separate buffer, navigate between them.

**Why Critical:**
- See all occurrences at once
- Quick navigation to matches
- Better than incremental search for many matches

**Implementation Priority:** 🟡 **MEDIUM**

**Key Operations:**
- `M-x occur` - Search and list matches
- `C-c C-c` - Go to occurrence
- `n` / `p` - Next/previous occurrence

**Current Gap:** Search exists but no occur mode.

---

#### 7. **Multiple Cursors**
**What:** Multiple cursor positions, edit at all positions simultaneously.

**Why Critical:**
- Modern editing expectation
- Edit multiple instances simultaneously
- Faster than find-replace for some cases

**Implementation Priority:** 🟡 **MEDIUM**

**Key Operations:**
- `C-n` - Add cursor at next match
- `C-p` - Add cursor at previous match
- `C-a` - Add cursor at all matches
- `Esc` - Exit multiple cursor mode

**Current Gap:** No multiple cursor support.

---

#### 8. **Undo Tree Visualization**
**What:** Visualize undo/redo history as tree, navigate branches.

**Why Critical:**
- Recover from wrong undo
- Explore alternative edit paths
- Essential for complex editing

**Implementation Priority:** 🟢 **LOW**

**Key Operations:**
- `C-x u` - Undo tree visualization
- Navigate branches
- Select alternative history

**Current Gap:** Linear undo/redo only.

---

#### 9. **Org-Mode**
**What:** Task management, notes, project planning, literate programming.

**Why Critical:**
- Developers love org-mode
- Project management in editor
- Document code with executable examples

**Implementation Priority:** 🟢 **LOW** (but high user value)

**Key Features:**
- TODO lists with states
- Time tracking
- Agenda views
- Code blocks with execution
- Export to multiple formats

**Current Gap:** No org-mode equivalent.

---

#### 10. **Dired (Directory Editor)**
**What:** File manager with bulk operations, regex operations, integration.

**Why Critical:**
- Powerful file operations
- Bulk rename/copy/delete
- Essential for file management workflows

**Implementation Priority:** 🟢 **LOW**

**Key Operations:**
- `C` - Copy marked files
- `D` - Delete marked files
- `R` - Rename file
- `m` - Mark file
- `*` - Mark by pattern
- `%` - Mark by regex

**Current Gap:** Basic file tree, no dired-like operations.

---

#### 11. **Abbrev Expansion**
**What:** Auto-expand abbreviations to full text (like snippets but simpler).

**Why Critical:**
- Quick text expansion
- Consistent terminology
- Less intrusive than snippets

**Implementation Priority:** 🟢 **LOW**

**Key Operations:**
- `M-x abbrev-mode` - Enable abbrev
- Define abbrevs
- Auto-expand on space/punctuation

**Current Gap:** No abbrev system.

---

#### 12. **Bookmark System**
**What:** Save positions in files, jump to bookmarks, organize by project.

**Why Critical:**
- Quick navigation to important locations
- Project-specific bookmarks
- Better than "recent files"

**Implementation Priority:** 🟢 **LOW**

**Key Operations:**
- `C-x r m` - Set bookmark
- `C-x r b` - Jump to bookmark
- `C-x r l` - List bookmarks

**Current Gap:** No bookmark system.

---

## Priority Recommendations

### 🔴 **Critical - Implement Soon**

1. **Pane Splitting** (tmux) - Essential for multitasking
2. **Copy Mode** (tmux) - Essential for terminal workflows
3. **Keyboard Macros** (emacs) - Powerful automation

### 🟡 **High Value - Consider Next**

4. **Synchronized Panes** (tmux) - DevOps workflows
5. **Register System** (emacs) - Multiple clipboards
6. **Mark & Point** (emacs) - Precise editing
7. **Rectangular Selection** (emacs) - Column operations
8. **Occur Mode** (emacs) - Better search UX
9. **Multiple Cursors** (emacs) - Modern expectation

### 🟢 **Nice to Have**

10. **Window Management** (tmux) - Organization
11. **Pane Layouts** (tmux) - Quick reorganization
12. **Narrowing** (emacs) - Focus editing
13. **Undo Tree** (emacs) - History navigation
14. **Org-Mode** (emacs) - Task management
15. **Dired** (emacs) - File operations
16. **Bookmarks** (emacs) - Navigation
17. **Abbrev** (emacs) - Text expansion

---

## Implementation Notes

### Pane Splitting Architecture

```purescript
-- Terminal pane state
type PaneState =
  { id :: String
  , terminal :: TerminalState
  , layout :: PaneLayout
  , parent :: Maybe String  -- Parent pane if split
  , children :: Array String  -- Child panes
  }

-- Split operations
splitPaneVertically :: PaneState -> Aff PaneState
splitPaneHorizontally :: PaneState -> Aff PaneState
resizePane :: PaneState -> Direction -> Int -> Aff PaneState
swapPanes :: String -> String -> Aff Unit
```

### Keyboard Macros Architecture

```purescript
-- Macro recording
type Macro =
  { name :: Maybe String
  , actions :: Array KeyboardAction
  , repeatCount :: Int
  }

-- Macro operations
startRecording :: Aff MacroId
stopRecording :: MacroId -> Aff Macro
executeMacro :: Macro -> Aff Unit
saveMacro :: Macro -> String -> Aff Unit
loadMacro :: String -> Aff Macro
```

---

## Conclusion

The most critical missing features are:

1. **Pane splitting** - Developers expect this from terminal tools
2. **Copy mode** - Essential for terminal workflows  
3. **Keyboard macros** - Powerful automation that emacs users expect

These three features would significantly improve developer productivity and align the tool with expectations from tmux/emacs power users.
