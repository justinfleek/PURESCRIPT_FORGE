-- | Undo/Redo State Management - History-Based State Restoration
-- |
-- | **What:** Provides undo/redo functionality by maintaining a history of application
-- |         states. Allows users to navigate backward and forward through state history.
-- | **Why:** Enables users to revert unwanted state changes and restore previous states.
-- |         Essential for user experience and error recovery.
-- | **How:** Maintains an array of states with a current index. Undo moves index backward,
-- |         redo moves index forward. New states are added to history, removing any future
-- |         states (branching history).
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Uses AppState for history storage
-- |
-- | **Mathematical Foundation:**
-- | - **History Invariant:** `0 <= currentIndex < length history` (index always valid)
-- | - **History Bounded:** History is bounded by `maxHistory` (default 50 states)
-- | - **Branching:** When a new state is added, all states after `currentIndex` are
-- |   removed (history branches, cannot redo after new action)
-- | - **Undo/Redo:** Undo decreases index, redo increases index. Both preserve history.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.UndoRedo as UndoRedo
-- |
-- | -- Check if undo/redo possible
-- | canUndo = UndoRedo.canUndo undoRedoState
-- | canRedo = UndoRedo.canRedo undoRedoState
-- |
-- | -- Undo
-- | case UndoRedo.undo undoRedoState of
-- |   Just newState -> -- Use newState
-- |   Nothing -> -- Cannot undo
-- |
-- | -- Add new state to history
-- | newUndoRedo = UndoRedo.pushState newAppState undoRedoState
-- | ```
-- |
-- | Based on spec 41-STATE-MANAGEMENT.md and audit requirements
module Sidepanel.State.UndoRedo where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Sidepanel.State.AppState (AppState)

-- | Undo/Redo state tracking - History state container
-- |
-- | **Purpose:** Maintains the undo/redo history with current position.
-- | **Fields:**
-- | - `history`: Array of application states (history)
-- | - `currentIndex`: Current position in history (0-based)
-- | - `maxHistory`: Maximum number of states to keep (default 50)
-- |
-- | **Invariants:**
-- | - `0 <= currentIndex < length history` (index always valid)
-- | - `length history <= maxHistory` (history bounded)
-- | - `length history > 0` (always at least one state)
-- |
-- | **Example:**
-- | ```purescript
-- | undoRedoState :: UndoRedoState
-- | undoRedoState = {
-- |   history: [state1, state2, state3]
-- |   , currentIndex: 1
-- |   , maxHistory: 50
-- | }
-- | ```
type UndoRedoState =
  { history :: Array AppState
  , currentIndex :: Int
  , maxHistory :: Int
  }

-- | Default maximum history size
defaultMaxHistory :: Int
defaultMaxHistory = 50

-- | Initial undo/redo state
initialUndoRedoState :: AppState -> UndoRedoState
initialUndoRedoState initialState =
  { history: [ initialState ]
  , currentIndex: 0
  , maxHistory: defaultMaxHistory
  }

-- | Check if undo is possible
canUndo :: UndoRedoState -> Boolean
canUndo state = state.currentIndex > 0

-- | Check if redo is possible - Can move forward in history
-- |
-- | **Purpose:** Determines if redo is possible (current index < last index).
-- | **Parameters:**
-- | - `state`: Undo/redo state to check
-- | **Returns:** True if redo is possible, false otherwise
-- | **Side Effects:** None (pure function)
canRedo :: UndoRedoState -> Boolean
canRedo state = state.currentIndex < Array.length state.history - 1

-- | Get current state from history
-- | Alias for getState
getCurrentState :: UndoRedoState -> Maybe AppState
getCurrentState = getState

-- | Add new state to history - Push state and update index
-- |
-- | **Purpose:** Adds a new state to history, removing any future states (branching
-- |             history). Trims history if it exceeds `maxHistory`.
-- | **Parameters:**
-- | - `newState`: New application state to add
-- | - `undoState`: Current undo/redo state
-- | **Returns:** Updated undo/redo state with new state added
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | 1. Removes all states after `currentIndex` (branching)
-- | 2. Appends `newState` to history
-- | 3. Trims history if it exceeds `maxHistory` (removes oldest states)
-- | 4. Updates `currentIndex` to point to new state
-- |
-- | **Example:**
-- | ```purescript
-- | newUndoRedo = pushState newAppState currentUndoRedo
-- | ```
pushState :: AppState -> UndoRedoState -> UndoRedoState
pushState newState undoState =
  let
    -- Remove any states after current index
    -- We are branching history
    historyBefore = Array.take (undoState.currentIndex + 1) undoState.history
    -- Add new state
    newHistory = Array.snoc historyBefore newState
    -- Trim history if it exceeds maxHistory
    trimmedHistory = if Array.length newHistory > undoState.maxHistory then
        Array.drop (Array.length newHistory - undoState.maxHistory) newHistory
      else
        newHistory
    -- Update index to point to new state
    newIndex = Array.length trimmedHistory - 1
  in
    undoState
      { history = trimmedHistory
      , currentIndex = newIndex
      }

-- | Undo: move back in history - Decrease current index
-- |
-- | **Purpose:** Moves backward in history by decreasing `currentIndex`.
-- | **Parameters:**
-- | - `state`: Current undo/redo state
-- | **Returns:** Updated undo/redo state if undo is possible, Nothing otherwise
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - If `canUndo state` is true: Returns state with `currentIndex` decreased by 1
-- | - Otherwise: Returns Nothing
-- |
-- | **Example:**
-- | ```purescript
-- | case undo currentState of
-- |   Just newState -> -- Use newState
-- |   Nothing -> -- Cannot undo
-- | ```
undo :: UndoRedoState -> Maybe UndoRedoState
undo state =
  if canUndo state then
    Just state { currentIndex = state.currentIndex - 1 }
  else
    Nothing

-- | Redo: move forward in history - Increase current index
-- |
-- | **Purpose:** Moves forward in history by increasing `currentIndex`.
-- | **Parameters:**
-- | - `state`: Current undo/redo state
-- | **Returns:** Updated undo/redo state if redo is possible, Nothing otherwise
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - If `canRedo state` is true: Returns state with `currentIndex` increased by 1
-- | - Otherwise: Returns Nothing
-- |
-- | **Example:**
-- | ```purescript
-- | case redo currentState of
-- |   Just newState -> -- Use newState
-- |   Nothing -> -- Cannot redo
-- | ```
redo :: UndoRedoState -> Maybe UndoRedoState
redo state =
  if canRedo state then
    Just state { currentIndex = state.currentIndex + 1 }
  else
    Nothing

-- | Get state at current index - Retrieve current state from history
-- |
-- | **Purpose:** Retrieves the application state at the current index in history.
-- | **Parameters:**
-- | - `state`: Undo/redo state
-- | **Returns:** Application state at current index, or Nothing if index invalid
-- | **Side Effects:** None (pure function)
-- |
-- | **Note:** Returns Nothing only if index is invalid, which should not happen
-- |          in normal operation (invariant ensures index is always valid).
-- |
-- | **Example:**
-- | ```purescript
-- | case getState undoRedoState of
-- |   Just appState -> -- Use appState
-- |   Nothing -> -- Should not happen
-- | ```
getState :: UndoRedoState -> Maybe AppState
getState state = Array.index state.history state.currentIndex
