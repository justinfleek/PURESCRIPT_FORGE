-- | Multi-Session Management - Session Tabs, Branching, and Parallel Conversations
-- |
-- | **What:** Manages multiple concurrent AI sessions with tabbed navigation, session
-- |         branching (fork a conversation to try different approaches), and session comparison.
-- | **Why:** Real coding workflows aren't linear - users need parallel exploration, context
-- |         separation, branching decisions, and comparison capabilities.
-- | **How:** Uses a tab-based UI with session metadata (title, icon, status), branching support
-- |         (parent/child relationships), and tab management (open, close, switch, reorder, pin).
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: SessionState type
-- |
-- | **Mathematical Foundation:**
-- | - **Tab Order Invariant:** `tabOrder` array contains exactly the IDs present in `tabs` array.
-- |   All tab IDs in `tabs` must be present in `tabOrder`.
-- | - **Active Tab Invariant:** `activeTabId` is `Nothing` or refers to a tab ID in `tabs`.
-- | - **Max Tabs Invariant:** `Array.length tabs <= maxTabs` (enforced when opening new tabs).
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.Sessions as Sessions
-- |
-- | -- Create initial tabs state
-- | tabsState :: SessionTabsState
-- | tabsState = Sessions.initialTabsState
-- |
-- | -- Open a new session tab
-- | newTabs = Sessions.openTab tabsState "session-123" "Debug Auth" "🔧"
-- | ```
-- |
-- | Based on spec 24-MULTI-SESSION-MANAGEMENT.md
module Sidepanel.State.Sessions where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Map as Map

-- | Session status - Current status of a session
-- |
-- | **Purpose:** Indicates whether a session is active, idle, archived, or deleted.
-- | **Values:**
-- | - `Active`: Currently in use
-- | - `Idle`: Open but not active
-- | - `Archived`: Stored but hidden
-- | - `Deleted`: Soft deleted (can be restored)
data SessionStatus = Active | Idle | Archived | Deleted

derive instance eqSessionStatus :: Eq SessionStatus

-- | Session tab - Tab representation for a session
-- |
-- | **Purpose:** Represents a session tab in the tabbed UI, including metadata and state.
-- | **Fields:**
-- | - `sessionId`: Session identifier (maps to session in sessions Map)
-- | - `title`: Display title for the tab
-- | - `icon`: Emoji icon for the tab
-- | - `isActive`: Whether this tab is currently active
-- | - `isDirty`: Whether the session has unsaved changes
-- | - `isPinned`: Whether the tab is pinned (cannot be closed easily)
-- |
-- | **Invariants:**
-- | - `sessionId` must exist in the sessions Map
-- | - Only one tab can have `isActive = true` at a time
type SessionTab =
  { sessionId :: String
  , title :: String
  , icon :: String
  , isActive :: Boolean
  , isDirty :: Boolean
  , isPinned :: Boolean
  }

-- | Session tabs state - State for managing session tabs
-- |
-- | **Purpose:** Manages the collection of open session tabs, their order, and active tab.
-- | **Fields:**
-- | - `tabs`: Array of session tabs (in display order)
-- | - `activeTabId`: Currently active tab ID (Nothing if no active tab)
-- | - `maxTabs`: Maximum number of tabs allowed (default 10)
-- | - `tabOrder`: Array of tab IDs in display order (for drag-and-drop reordering)
-- |
-- | **Invariants:**
-- | - `tabOrder` contains exactly the IDs present in `tabs`
-- | - `activeTabId` is `Nothing` or refers to a tab ID in `tabs`
-- | - `Array.length tabs <= maxTabs`
type SessionTabsState =
  { tabs :: Array SessionTab
  , activeTabId :: Maybe String
  , maxTabs :: Int
  , tabOrder :: Array String
  }

-- | Session metadata - Extended metadata for sessions (beyond SessionState)
-- |
-- | **Purpose:** Stores additional metadata for sessions that isn't in SessionState,
-- |             including branching information, status, and display properties.
-- | **Fields:**
-- | - `title`: Display title
-- | - `icon`: Emoji icon
-- | - `color`: Optional color theme
-- | - `status`: Session status (active, idle, archived, deleted)
-- | - `parentId`: Parent session ID if this is a branch (Nothing if root session)
-- | - `branchPoint`: Message index where branched (Nothing if not a branch)
-- | - `children`: Array of child branch IDs
-- |
-- | **Invariants:**
-- | - If `parentId` is `Just id`, then `branchPoint` must be `Just n` (n >= 0)
-- | - If `parentId` is `Nothing`, then `branchPoint` must be `Nothing`
type SessionMetadata =
  { title :: String
  , icon :: String
  , color :: Maybe String
  , status :: SessionStatus
  , parentId :: Maybe String
  , branchPoint :: Maybe Int
  , children :: Array String
  }

-- | Initial tabs state - Default session tabs state
-- |
-- | **Purpose:** Creates the initial session tabs state with no tabs, no active tab,
-- |             and default max tabs (10).
-- | **Returns:** SessionTabsState with all fields initialized to defaults
-- | **Side Effects:** None (pure function)
initialTabsState :: SessionTabsState
initialTabsState =
  { tabs: []
  , activeTabId: Nothing
  , maxTabs: 10
  , tabOrder: []
  }

-- | Open tab - Add a new session tab
-- |
-- | **Purpose:** Opens a new session tab, making it active. If max tabs reached,
-- |             removes the oldest inactive tab (or oldest tab if all are active).
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to open
-- | - `title`: Tab title
-- | - `icon`: Tab icon (emoji)
-- | **Returns:** Updated tabs state with new tab added and set as active
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - If max tabs reached: Removes oldest inactive tab, or oldest tab if all active
-- | - New tab is added to end of `tabOrder` and `tabs` array
-- | - All other tabs have `isActive` set to false
-- | - New tab has `isActive = true`
openTab :: SessionTabsState -> String -> String -> String -> SessionTabsState
openTab state sessionId title icon =
  let
    -- Check if tab already exists
    existingIndex = Array.findIndex (\t -> t.sessionId == sessionId) state.tabs
    
    -- If exists, just activate it
    updatedTabs = case existingIndex of
      Just idx ->
        Array.mapWithIndex (\i t ->
          if i == idx
            then t { isActive = true }
            else t { isActive = false }
        ) state.tabs
      Nothing ->
        let
          -- Check if we need to remove a tab (max tabs reached)
          needsRemoval = Array.length state.tabs >= state.maxTabs
          tabsToKeep = if needsRemoval then
              -- Remove oldest inactive tab, or oldest tab if all active
              let
                inactiveTabs = Array.findIndex (\t -> not t.isActive) state.tabs
                indexToRemove = case inactiveTabs of
                  Just idx -> idx
                  Nothing -> 0  -- Remove first tab if all active
                removedTab = Array.index state.tabs indexToRemove
                newTabs = Array.deleteAt indexToRemove state.tabs
                newTabOrder = case removedTab of
                  Just tab -> Array.filter (\id -> id /= tab.sessionId) state.tabOrder
                  Nothing -> state.tabOrder
              in
                { tabs: case newTabs of
                    Just ts -> ts
                    Nothing -> state.tabs
                , tabOrder: newTabOrder
                }
            else
              { tabs: state.tabs, tabOrder: state.tabOrder }
          
          -- Create new tab
          newTab =
            { sessionId: sessionId
            , title: title
            , icon: icon
            , isActive: true
            , isDirty: false
            , isPinned: false
            }
          
          -- Deactivate all existing tabs
          deactivatedTabs = Array.map (\t -> t { isActive = false }) tabsToKeep.tabs
          
          -- Add new tab
          updatedTabsArray = Array.snoc deactivatedTabs newTab
          updatedTabOrder = Array.snoc tabsToKeep.tabOrder sessionId
        in
          updatedTabsArray
  in
    state
      { tabs = updatedTabs
      , activeTabId = Just sessionId
      , tabOrder = case existingIndex of
          Just _ -> state.tabOrder  -- Keep existing order if tab already exists
          Nothing -> Array.snoc state.tabOrder sessionId  -- Add to end if new
      }

-- | Close tab - Remove a session tab
-- |
-- | **Purpose:** Closes a session tab. If the closed tab was active, activates the
-- |             next tab (or previous if last tab). Pinned tabs cannot be closed.
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to close
-- | **Returns:** Updated tabs state with tab removed (or unchanged if pinned)
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - If tab is pinned: Returns state unchanged
-- | - If closed tab was active: Activates next tab (or previous if last)
-- | - Removes tab from both `tabs` and `tabOrder` arrays
closeTab :: SessionTabsState -> String -> SessionTabsState
closeTab state sessionId =
  let
    tabToClose = Array.find (\t -> t.sessionId == sessionId) state.tabs
    
    -- Check if pinned
    isPinned = case tabToClose of
      Just tab -> tab.isPinned
      Nothing -> false
    
    -- If pinned, don't close
    if isPinned then
      state
    else
      let
        -- Remove tab
        updatedTabs = Array.filter (\t -> t.sessionId /= sessionId) state.tabs
        updatedTabOrder = Array.filter (\id -> id /= sessionId) state.tabOrder
        
        -- If closed tab was active, activate next tab (or previous if last)
        wasActive = case tabToClose of
          Just tab -> tab.isActive
          Nothing -> false
        
        -- Find index of closed tab in original order
        closedIndex = Array.findIndex (\id -> id == sessionId) state.tabOrder
        
        -- Determine new active tab
        newActiveTabId = if wasActive then
            case closedIndex of
              Just idx ->
                -- Try next tab, or previous if last
                if idx < Array.length state.tabOrder - 1 then
                  Array.index updatedTabOrder idx  -- Next tab
                else if idx > 0 then
                  Array.index updatedTabOrder (idx - 1)  -- Previous tab
                else
                  Nothing  -- No tabs left
              Nothing -> state.activeTabId  -- Tab not found, keep current active
          else
            state.activeTabId  -- Closed tab wasn't active, keep current active
        
        -- Update active state
        finalTabs = case newActiveTabId of
          Just activeId ->
            Array.map (\t ->
              if t.sessionId == activeId
                then t { isActive = true }
                else t { isActive = false }
            ) updatedTabs
          Nothing ->
            Array.map (\t -> t { isActive = false }) updatedTabs
      in
        state
          { tabs = finalTabs
          , activeTabId = newActiveTabId
          , tabOrder = updatedTabOrder
          }

-- | Switch to tab - Activate a different tab
-- |
-- | **Purpose:** Switches the active tab to the specified session ID.
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to activate
-- | **Returns:** Updated tabs state with specified tab active
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - Sets `isActive = true` for specified tab
-- | - Sets `isActive = false` for all other tabs
-- | - Updates `activeTabId` to specified session ID
switchToTab :: SessionTabsState -> String -> SessionTabsState
switchToTab state sessionId =
  let
    updatedTabs = Array.map (\t ->
      if t.sessionId == sessionId
        then t { isActive = true }
        else t { isActive = false }
    ) state.tabs
  in
    state
      { tabs = updatedTabs
      , activeTabId = Just sessionId
      }

-- | Reorder tabs - Change tab display order
-- |
-- | **Purpose:** Reorders tabs based on a new array of session IDs (from drag-and-drop).
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `newOrder`: New array of session IDs in display order
-- | **Returns:** Updated tabs state with tabs reordered
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - Reorders `tabs` array to match `newOrder`
-- | - Updates `tabOrder` to `newOrder`
-- | - Preserves all tab properties (only order changes)
reorderTabs :: SessionTabsState -> Array String -> SessionTabsState
reorderTabs state newOrder =
  let
    -- Create Map for quick lookup
    tabMap = Map.fromFoldable $ Array.map (\t -> t.sessionId /\ t) state.tabs
    
    -- Reorder tabs based on newOrder
    reorderedTabs = Array.mapMaybe (\id -> Map.lookup id tabMap) newOrder
  in
    state
      { tabs = reorderedTabs
      , tabOrder = newOrder
      }

-- | Pin tab - Pin a tab (prevents closing)
-- |
-- | **Purpose:** Pins a tab, preventing it from being closed.
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to pin
-- | **Returns:** Updated tabs state with tab pinned
-- | **Side Effects:** None (pure function)
pinTab :: SessionTabsState -> String -> SessionTabsState
pinTab state sessionId =
  let
    updatedTabs = Array.map (\t ->
      if t.sessionId == sessionId
        then t { isPinned = true }
        else t
    ) state.tabs
  in
    state { tabs = updatedTabs }

-- | Unpin tab - Unpin a tab (allows closing)
-- |
-- | **Purpose:** Unpins a tab, allowing it to be closed.
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to unpin
-- | **Returns:** Updated tabs state with tab unpinned
-- | **Side Effects:** None (pure function)
unpinTab :: SessionTabsState -> String -> SessionTabsState
unpinTab state sessionId =
  let
    updatedTabs = Array.map (\t ->
      if t.sessionId == sessionId
        then t { isPinned = false }
        else t
    ) state.tabs
  in
    state { tabs = updatedTabs }

-- | Rename tab - Change tab title
-- |
-- | **Purpose:** Renames a tab's display title.
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to rename
-- | - `newTitle`: New title
-- | **Returns:** Updated tabs state with tab renamed
-- | **Side Effects:** None (pure function)
renameTab :: SessionTabsState -> String -> String -> SessionTabsState
renameTab state sessionId newTitle =
  let
    updatedTabs = Array.map (\t ->
      if t.sessionId == sessionId
        then t { title = newTitle }
        else t
    ) state.tabs
  in
    state { tabs = updatedTabs }

-- | Set tab icon - Change tab icon
-- |
-- | **Purpose:** Changes a tab's emoji icon.
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID
-- | - `newIcon`: New icon (emoji)
-- | **Returns:** Updated tabs state with tab icon updated
-- | **Side Effects:** None (pure function)
setTabIcon :: SessionTabsState -> String -> String -> SessionTabsState
setTabIcon state sessionId newIcon =
  let
    updatedTabs = Array.map (\t ->
      if t.sessionId == sessionId
        then t { icon = newIcon }
        else t
    ) state.tabs
  in
    state { tabs = updatedTabs }

-- | Mark tab dirty - Mark tab as having unsaved changes
-- |
-- | **Purpose:** Marks a tab as dirty (has unsaved changes), typically shown with a dot indicator.
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to mark dirty
-- | **Returns:** Updated tabs state with tab marked dirty
-- | **Side Effects:** None (pure function)
markTabDirty :: SessionTabsState -> String -> SessionTabsState
markTabDirty state sessionId =
  let
    updatedTabs = Array.map (\t ->
      if t.sessionId == sessionId
        then t { isDirty = true }
        else t
    ) state.tabs
  in
    state { tabs = updatedTabs }

-- | Mark tab clean - Mark tab as having no unsaved changes
-- |
-- | **Purpose:** Marks a tab as clean (no unsaved changes).
-- | **Parameters:**
-- | - `state`: Current tabs state
-- | - `sessionId`: Session ID to mark clean
-- | **Returns:** Updated tabs state with tab marked clean
-- | **Side Effects:** None (pure function)
markTabClean :: SessionTabsState -> String -> SessionTabsState
markTabClean state sessionId =
  let
    updatedTabs = Array.map (\t ->
      if t.sessionId == sessionId
        then t { isDirty = false }
        else t
    ) state.tabs
  in
    state { tabs = updatedTabs }
