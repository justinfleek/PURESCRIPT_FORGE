-- | Sync context - manages session data synchronization
-- | Migrated from: forge-dev/packages/app/src/context/sync.tsx
module Sidepanel.Context.Sync
  ( SyncState
  , Message
  , MessageRole
  , MessageTime
  , Part
  , Session
  , SessionHistory
  , mkSyncState
  , keyFor
  , getSession
  , hasMoreHistory
  , isHistoryLoading
  , SessionTime
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)

-- | Message role
type MessageRole = String -- "user" | "assistant"

-- | Message timestamp
type MessageTime =
  { created :: Number
  }

-- | Message
type Message =
  { id :: String
  , sessionID :: String
  , role :: MessageRole
  , time :: MessageTime
  , agent :: String
  , model :: { providerID :: String, modelID :: String }
  }

-- | Part (message content)
type Part =
  { id :: String
  , messageID :: String
  , partType :: String
  , content :: Maybe String
  }

-- | Session time info
type SessionTime =
  { created :: Number
  , updated :: Maybe Number
  , archived :: Maybe Number
  }

-- | Session
type Session =
  { id :: String
  , title :: Maybe String
  , parentID :: Maybe String
  , time :: SessionTime
  }

-- | Session history metadata
type SessionHistory =
  { limit :: Int
  , complete :: Boolean
  , loading :: Boolean
  }

-- | Sync state
type SyncState =
  { messages :: Map String (Array Message)
  , parts :: Map String (Array Part)
  , sessions :: Array Session
  , history :: Map String SessionHistory
  }

-- | Default chunk size
defaultChunk :: Int
defaultChunk = 400

-- | Create initial sync state
mkSyncState :: SyncState
mkSyncState =
  { messages: Map.empty
  , parts: Map.empty
  , sessions: []
  , history: Map.empty
  }

-- | Generate key for directory/session
keyFor :: String -> String -> String
keyFor directory sessionID = directory <> "\n" <> sessionID

-- | Get session by ID using binary search
getSession :: String -> SyncState -> Maybe Session
getSession sessionID state =
  binarySearch sessionID state.sessions
  where
    binarySearch :: String -> Array Session -> Maybe Session
    binarySearch target arr = go 0 (Array.length arr - 1)
      where
        go lo hi
          | lo > hi = Nothing
          | otherwise =
              let mid = lo + (hi - lo) / 2
              in case Array.index arr mid of
                Nothing -> Nothing
                Just s ->
                  case compare s.id target of
                    LT -> go (mid + 1) hi
                    GT -> go lo (mid - 1)
                    EQ -> Just s

-- | Check if there's more history to load
hasMoreHistory :: String -> String -> SyncState -> Boolean
hasMoreHistory directory sessionID state =
  let key = keyFor directory sessionID
  in case Map.lookup key state.history of
    Nothing -> false
    Just h -> not h.complete

-- | Check if history is currently loading
isHistoryLoading :: String -> String -> SyncState -> Boolean
isHistoryLoading directory sessionID state =
  let key = keyFor directory sessionID
  in case Map.lookup key state.history of
    Nothing -> false
    Just h -> h.loading
