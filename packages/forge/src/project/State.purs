{-|
Module      : Forge.Project.State
Description : Project State Management

Persistent state management for projects. Stores and retrieves
project-specific state that persists across sessions.
-}
module Forge.Project.State
  ( -- * Types
    ProjectState
  , StateKey
    -- * State Operations
  , getState
  , setState
  , updateState
  , clearState
    -- * State Queries
  , hasState
  , getLastUpdated
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | State key
type StateKey = String

-- | Project state
type ProjectState =
  { isInitialized :: Boolean
  , hasConfig :: Boolean
  , lastUpdated :: Number
  , lastSessionId :: Maybe String
  , settings :: Maybe String  -- JSON settings
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import loadStateFFI :: String -> Aff (Maybe ProjectState)
foreign import saveStateFFI :: String -> ProjectState -> Aff (Either String Unit)
foreign import deleteStateFFI :: String -> Aff (Either String Unit)
foreign import nowFFI :: Aff Number

-- ============================================================================
-- STATE OPERATIONS
-- ============================================================================

{-| Get project state.

Loads state from .forge/state.json in the project directory.
-}
getState :: String -> Aff (Either String ProjectState)
getState projectId = do
  result <- loadStateFFI projectId
  case result of
    Nothing -> do
      -- Return default state
      now <- nowFFI
      pure $ Right
        { isInitialized: false
        , hasConfig: false
        , lastUpdated: now
        , lastSessionId: Nothing
        , settings: Nothing
        }
    Just state -> pure $ Right state

{-| Set project state.

Saves state to .forge/state.json in the project directory.
-}
setState :: String -> ProjectState -> Aff (Either String Unit)
setState projectId state = do
  now <- nowFFI
  saveStateFFI projectId state { lastUpdated = now }

{-| Update project state with a function. -}
updateState :: String -> (ProjectState -> ProjectState) -> Aff (Either String Unit)
updateState projectId updateFn = do
  currentResult <- getState projectId
  case currentResult of
    Left err -> pure $ Left err
    Right current -> setState projectId (updateFn current)

{-| Clear project state. -}
clearState :: String -> Aff (Either String Unit)
clearState = deleteStateFFI

-- ============================================================================
-- STATE QUERIES
-- ============================================================================

{-| Check if project has state. -}
hasState :: String -> Aff Boolean
hasState projectId = do
  result <- loadStateFFI projectId
  pure $ case result of
    Nothing -> false
    Just _ -> true

{-| Get last updated timestamp. -}
getLastUpdated :: String -> Aff (Maybe Number)
getLastUpdated projectId = do
  result <- loadStateFFI projectId
  pure $ map _.lastUpdated result
