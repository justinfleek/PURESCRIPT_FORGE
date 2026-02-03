-- | Layout scroll persistence utilities
-- | Migrated from: forge-dev/packages/app/src/context/layout-scroll.ts
module App.Context.LayoutScroll
  ( SessionScroll
  , ScrollMap
  , ScrollPersistence
  , mkScrollPersistence
  , getScroll
  , setScroll
  , flush
  , flushAll
  , dropKeys
  , cloneScrollMap
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Data.Array (foldl)

-- | Scroll position for a session
type SessionScroll =
  { x :: Number
  , y :: Number
  }

-- | Map of tab -> scroll position
type ScrollMap = Map String SessionScroll

-- | Scroll persistence state
type ScrollPersistence =
  { cache :: Map String ScrollMap
  , dirty :: Set String
  , debounceMs :: Int
  }

-- | Create initial scroll persistence
mkScrollPersistence :: Int -> ScrollPersistence
mkScrollPersistence debounceMs =
  { cache: Map.empty
  , dirty: Set.empty
  , debounceMs
  }

-- | Clone a scroll map (for immutability)
cloneScrollMap :: Maybe ScrollMap -> ScrollMap
cloneScrollMap Nothing = Map.empty
cloneScrollMap (Just m) = m -- Maps are already immutable in PureScript

-- | Seed the cache if not present
seed :: ScrollPersistence -> String -> Maybe ScrollMap -> ScrollPersistence
seed state sessionKey snapshot =
  case Map.lookup sessionKey state.cache of
    Just _ -> state
    Nothing -> state { cache = Map.insert sessionKey (cloneScrollMap snapshot) state.cache }

-- | Get scroll position for a session/tab
getScroll :: ScrollPersistence -> String -> String -> Maybe SessionScroll
getScroll state sessionKey tab =
  case Map.lookup sessionKey state.cache of
    Nothing -> Nothing
    Just scrollMap -> Map.lookup tab scrollMap

-- | Set scroll position for a session/tab
setScroll :: ScrollPersistence -> String -> String -> SessionScroll -> Maybe ScrollMap -> ScrollPersistence
setScroll state sessionKey tab pos snapshot =
  let
    seeded = seed state sessionKey snapshot
    cache = seeded.cache
    scrollMap = fromMaybe Map.empty (Map.lookup sessionKey cache)
    prev = Map.lookup tab scrollMap
    
    -- Check if position actually changed
    unchanged = case prev of
      Nothing -> false
      Just p -> p.x == pos.x && p.y == pos.y
  in
    if unchanged
    then seeded
    else
      let
        newScrollMap = Map.insert tab pos scrollMap
        newCache = Map.insert sessionKey newScrollMap cache
        newDirty = Set.insert sessionKey seeded.dirty
      in
        seeded { cache = newCache, dirty = newDirty }

-- | Flush a session's scroll state
flush :: ScrollPersistence -> String -> { state :: ScrollPersistence, flushed :: Maybe ScrollMap }
flush state sessionKey =
  if not (Set.member sessionKey state.dirty)
  then { state, flushed: Nothing }
  else
    let
      newDirty = Set.delete sessionKey state.dirty
      flushed = Map.lookup sessionKey state.cache
    in
      { state: state { dirty = newDirty }, flushed }

-- | Flush all dirty sessions
flushAll :: ScrollPersistence -> { state :: ScrollPersistence, flushed :: Array { key :: String, scroll :: ScrollMap } }
flushAll state =
  let
    keys = Set.toUnfoldable state.dirty :: Array String
    
    result = foldl (\acc key ->
      case Map.lookup key state.cache of
        Nothing -> acc
        Just scroll -> acc <> [{ key, scroll }]
    ) [] keys
    
    newDirty = Set.empty
  in
    { state: state { dirty = newDirty }, flushed: result }

-- | Drop specific session keys from cache
dropKeys :: ScrollPersistence -> Array String -> ScrollPersistence
dropKeys state keys =
  let
    newCache = foldl (\c key -> Map.delete key c) state.cache keys
    newDirty = foldl (\d key -> Set.delete key d) state.dirty keys
  in
    state { cache = newCache, dirty = newDirty }
