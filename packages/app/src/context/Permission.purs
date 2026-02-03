-- | Permission context - manages auto-accept permissions
-- | Migrated from: forge-dev/packages/app/src/context/permission.tsx
module App.Context.Permission
  ( PermissionRequest
  , PermissionResponse(..)
  , PermissionStore
  , mkPermissionStore
  , shouldAutoAccept
  , isAutoAccepting
  , enableAutoAccept
  , disableAutoAccept
  , toggleAutoAccept
  , hasAutoAcceptPermissionConfig
  , acceptKey
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set

-- | Permission request from server
type PermissionRequest =
  { id :: String
  , sessionID :: String
  , permission :: String
  , metadata :: Maybe String
  }

-- | Permission response type
data PermissionResponse
  = Once
  | Always
  | Reject

derive instance eqPermissionResponse :: Eq PermissionResponse

instance showPermissionResponse :: Show PermissionResponse where
  show Once = "once"
  show Always = "always"
  show Reject = "reject"

-- | Permission store state
type PermissionStore =
  { autoAcceptEdits :: Map String Boolean
  , responded :: Set String  -- Recently responded permission IDs
  }

-- | Create initial permission store
mkPermissionStore :: PermissionStore
mkPermissionStore =
  { autoAcceptEdits: Map.empty
  , responded: Set.empty
  }

-- | Check if permission should be auto-accepted
shouldAutoAccept :: PermissionRequest -> Boolean
shouldAutoAccept perm = perm.permission == "edit"

-- | Generate key for auto-accept tracking
acceptKey :: String -> Maybe String -> String
acceptKey sessionID Nothing = sessionID
acceptKey sessionID (Just directory) = directory <> "/" <> sessionID

-- | Check if auto-accepting is enabled for a session
isAutoAccepting :: PermissionStore -> String -> Maybe String -> Boolean
isAutoAccepting store sessionID directory =
  let
    key = acceptKey sessionID directory
    directLookup = Map.lookup key store.autoAcceptEdits
    fallback = Map.lookup sessionID store.autoAcceptEdits
  in
    fromMaybe (fromMaybe false fallback) directLookup

-- | Enable auto-accept for a session
enableAutoAccept :: String -> String -> PermissionStore -> PermissionStore
enableAutoAccept sessionID directory store =
  let
    key = acceptKey sessionID (Just directory)
    -- Remove legacy key and add new key
    updated = store.autoAcceptEdits
      # Map.delete sessionID
      # Map.insert key true
  in
    store { autoAcceptEdits = updated }

-- | Disable auto-accept for a session
disableAutoAccept :: String -> Maybe String -> PermissionStore -> PermissionStore
disableAutoAccept sessionID directory store =
  let
    keyToRemove = case directory of
      Just dir -> acceptKey sessionID (Just dir)
      Nothing -> sessionID
    updated = store.autoAcceptEdits
      # Map.delete keyToRemove
      # Map.delete sessionID
  in
    store { autoAcceptEdits = updated }

-- | Toggle auto-accept for a session
toggleAutoAccept :: String -> String -> PermissionStore -> PermissionStore
toggleAutoAccept sessionID directory store =
  if isAutoAccepting store sessionID (Just directory)
  then disableAutoAccept sessionID (Just directory) store
  else enableAutoAccept sessionID directory store

-- | Check if a permission config value indicates auto-accept is configured
hasAutoAcceptPermissionConfig :: Maybe String -> Boolean
hasAutoAcceptPermissionConfig Nothing = false
hasAutoAcceptPermissionConfig (Just permission) =
  permission /= "allow"

-- | Helper to check non-allow rules
isNonAllowRule :: Maybe String -> Boolean
isNonAllowRule Nothing = false
isNonAllowRule (Just rule) = rule /= "allow"
