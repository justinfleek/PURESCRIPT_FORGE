-- | Persistence utilities for localStorage with caching and migration
-- | Migrated from: forge-dev/packages/app/src/utils/persist.ts (452 lines)
module Sidepanel.Utils.Persist
  ( Persist
  , PersistTarget
  , persisted
  , removePersisted
  , global
  , workspace
  , session
  , scoped
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign (Foreign)

-- | Persistence target configuration
type PersistTarget =
  { storage :: Maybe String
  , key :: String
  , legacy :: Array String
  , migrate :: Maybe (Foreign -> Foreign)
  }

-- | Storage file names
globalStorage :: String
globalStorage = "forge.global.dat"

legacyStorage :: String
legacyStorage = "default.dat"

localPrefix :: String
localPrefix = "forge."

-- | Cache configuration
cacheMaxEntries :: Int
cacheMaxEntries = 500

cacheMaxBytes :: Int
cacheMaxBytes = 8 * 1024 * 1024  -- 8MB

-- | Cache entry type
type CacheEntry =
  { value :: String
  , bytes :: Int
  }

-- | Module-level cache state
foreign import cache :: Ref (Map String CacheEntry)
foreign import cacheTotal :: Ref Int
foreign import fallbackDisabled :: Ref Boolean

-- | Delete from cache
cacheDelete :: String -> Effect Unit
cacheDelete key = do
  cacheMap <- Ref.read cache
  case Map.lookup key cacheMap of
    Nothing -> pure unit
    Just entry -> do
      Ref.modify (_ - entry.bytes) cacheTotal
      Ref.modify (Map.delete key) cache

-- | Prune cache to stay within limits
cachePrune :: Effect Unit
cachePrune = do
  size <- Map.size <$> Ref.read cache
  total <- Ref.read cacheTotal
  when (size > cacheMaxEntries || total > cacheMaxBytes) do
    cacheMap <- Ref.read cache
    case Map.findMin cacheMap of
      Nothing -> pure unit
      Just { key, value } -> do
        cacheDelete key
        cachePrune

-- | Set cache entry
cacheSet :: String -> String -> Effect Unit
cacheSet key value = do
  let bytes = 2 * stringLength value  -- UTF-16 characters = 2 bytes each
  when (bytes <= cacheMaxBytes) do
    cacheDelete key
    Ref.modify (Map.insert key { value, bytes }) cache
    Ref.modify (_ + bytes) cacheTotal
    cachePrune

-- | Get from cache
cacheGet :: String -> Effect (Maybe String)
cacheGet key = do
  cacheMap <- Ref.read cache
  case Map.lookup key cacheMap of
    Nothing -> pure Nothing
    Just entry -> do
      -- Move to end (LRU)
      Ref.modify (Map.delete key) cache
      Ref.modify (Map.insert key entry) cache
      pure (Just entry.value)

-- | Check if error is quota exceeded
isQuotaError :: Foreign -> Boolean
isQuotaError = isQuotaErrorImpl

foreign import isQuotaErrorImpl :: Foreign -> Boolean

-- | Evict items to make room
foreign import evict :: String -> String -> Effect Boolean

-- | Write to storage with quota handling
foreign import writeToStorage :: String -> String -> Effect Boolean

-- | Merge defaults with stored value
merge :: Foreign -> Foreign -> Foreign
merge defaults value = mergeImpl defaults value

foreign import mergeImpl :: Foreign -> Foreign -> Foreign

-- | Parse JSON safely
foreign import parseJson :: String -> Maybe Foreign

-- | Stringify value
foreign import jsonStringify :: Foreign -> String

-- | Get workspace storage name from directory
workspaceStorage :: String -> String
workspaceStorage dir =
  let head = take 12 dir
      sum = checksum dir
  in "forge.workspace." <> head <> "." <> sum <> ".dat"

foreign import checksum :: String -> String
foreign import take :: Int -> String -> String
foreign import stringLength :: String -> Int

-- | Persist namespace
type Persist =
  { global :: String -> Array String -> PersistTarget
  , workspace :: String -> String -> Array String -> PersistTarget
  , session :: String -> String -> String -> Array String -> PersistTarget
  , scoped :: String -> Maybe String -> String -> Array String -> PersistTarget
  }

-- | Create global persist target
global :: String -> Array String -> PersistTarget
global key legacy =
  { storage: Just globalStorage
  , key
  , legacy
  , migrate: Nothing
  }

-- | Create workspace persist target
workspace :: String -> String -> Array String -> PersistTarget
workspace dir key legacy =
  { storage: Just (workspaceStorage dir)
  , key: "workspace:" <> key
  , legacy
  , migrate: Nothing
  }

-- | Create session persist target
session :: String -> String -> String -> Array String -> PersistTarget
session dir sessionId key legacy =
  { storage: Just (workspaceStorage dir)
  , key: "session:" <> sessionId <> ":" <> key
  , legacy
  , migrate: Nothing
  }

-- | Create scoped persist target (session if available, else workspace)
scoped :: String -> Maybe String -> String -> Array String -> PersistTarget
scoped dir maybeSession key legacy = case maybeSession of
  Just sessionId -> session dir sessionId key legacy
  Nothing -> workspace dir key legacy

-- | Remove persisted value
removePersisted :: PersistTarget -> Effect Unit
removePersisted target = removePersistedImpl target.storage target.key

foreign import removePersistedImpl :: Maybe String -> String -> Effect Unit

-- | Create persisted store
-- | Returns [store, setStore, init, ready]
-- | Uses makePersisted from solid-primitives under the hood
persisted :: forall a. PersistTarget -> Tuple (Store a) (SetStore a) -> PersistedResult a
persisted target store = persistedImpl target store

type Store a = a
type SetStore a = a -> Effect Unit
type PersistedResult a =
  { store :: Store a
  , setStore :: SetStore a
  , init :: Maybe (Aff String)
  , ready :: Effect Boolean
  }

foreign import persistedImpl :: forall a. PersistTarget -> Tuple (Store a) (SetStore a) -> PersistedResult a
