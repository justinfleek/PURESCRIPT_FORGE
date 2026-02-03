-- | PureScript type definitions for Forge State types
-- | Phase 2: Type Safety Layer
module Forge.Types.State where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (Json)

-- | Project state information
type ProjectState =
  { id :: String
  , worktree :: String
  , vcs :: Maybe String
  , name :: Maybe String
  , created :: Number
  , updated :: Number
  }

-- | Project time information
type ProjectTime =
  { created :: Number
  , updated :: Number
  , initialized :: Maybe Number
  }

-- | Sync status
data SyncStatus = Loading | Partial | Complete

derive instance genericSyncStatus :: Generic SyncStatus _
derive instance eqSyncStatus :: Eq SyncStatus

instance showSyncStatus :: Show SyncStatus where
  show = genericShow

-- | UI sync state (simplified)
type UISyncState =
  { status :: SyncStatus
  , sessionCount :: Int
  , messageCount :: Int
  }
