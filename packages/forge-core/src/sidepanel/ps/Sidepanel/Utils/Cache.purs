-- | Memory Cache Utilities - TTL-Based Caching System
-- |
-- | **What:** Provides an in-memory caching system with Time-To-Live (TTL) support for
-- |         performance optimization. Caches key-value pairs with automatic expiry.
-- | **Why:** Reduces redundant computations and API calls by caching results with configurable
-- |         expiry times. Improves application performance and reduces server load.
-- | **How:** Uses Effect.Ref and Data.Map to store cache entries with expiry timestamps.
-- |         Automatically removes expired entries on access. Supports cleanup of all expired
-- |         entries.
-- |
-- | **Dependencies:**
-- | - `Effect.Ref`: Mutable reference for cache storage
-- | - `Data.Map`: Key-value map for cache entries
-- |
-- | **Mathematical Foundation:**
-- | - **Expiry Calculation:** `expiryTime = currentTime + TTL`. Entries are expired if
-- |   `currentTime > expiryTime`.
-- | - **Cache Entry:** `{ value: v, expiryTime: Number }` where `expiryTime` is milliseconds
-- |   since epoch.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Utils.Cache as Cache
-- | import Data.Time.Duration (Milliseconds(..))
-- |
-- | -- Create cache with 5 minute default TTL
-- | cache <- Cache.createCache (Milliseconds 300000.0)
-- |
-- | -- Set value
-- | Cache.set cache "key" "value" Nothing  -- Uses default TTL
-- | Cache.set cache "key" "value" (Just (Milliseconds 60000.0))  -- 1 minute TTL
-- |
-- | -- Get value (returns Nothing if expired or not found)
-- | value <- Cache.get cache "key"
-- |
-- | -- Cleanup expired entries
-- | expiredCount <- Cache.cleanupExpired cache
-- | ```
-- |
-- | Based on NEXUS/performance/src/cache.py
module Sidepanel.Utils.Cache where

import Prelude
import Effect (Effect)
import Effect.Ref as Ref
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Time.Duration (Milliseconds(..))
import Data.Int (toNumber)

-- | Cache entry with expiry time
type CacheEntry v =
  { value :: v
  , expiryTime :: Number -- milliseconds since epoch
  }

-- | Cache with TTL support
type Cache k v =
  { entries :: Ref.Ref (Map.Map k (CacheEntry v))
  , defaultTTL :: Milliseconds
  }

-- | Create a new cache with default TTL
createCache :: forall k v. Ord k => Milliseconds -> Effect (Cache k v)
createCache defaultTTL = do
  entries <- Ref.new Map.empty
  pure { entries, defaultTTL }

-- | Get value from cache (returns Nothing if expired or not found)
get :: forall k v. Ord k => Cache k v -> k -> Effect (Maybe v)
get cache key = do
  entries <- Ref.read cache.entries
  case Map.lookup key entries of
    Nothing -> pure Nothing
    Just entry -> do
      now <- getCurrentTimeMs
      if now > entry.expiryTime then
        -- Expired, remove and return Nothing
        Ref.modify_ (Map.delete key) cache.entries *> pure Nothing
      else
        pure (Just entry.value)

-- | Set value in cache with optional TTL (uses default if not provided)
set :: forall k v. Ord k => Cache k v -> k -> v -> Maybe Milliseconds -> Effect Unit
set cache key value maybeTTL = do
  now <- getCurrentTimeMs
  let ttl = fromMaybe cache.defaultTTL maybeTTL
  let expiryTime = now + (toNumber $ unwrap ttl)
  let entry = { value, expiryTime }
  Ref.modify_ (Map.insert key entry) cache.entries

-- | Delete key from cache
delete :: forall k v. Ord k => Cache k v -> k -> Effect Unit
delete cache key = Ref.modify_ (Map.delete key) cache.entries

-- | Clear all cache entries
clear :: forall k v. Cache k v -> Effect Unit
clear cache = Ref.write Map.empty cache.entries

-- | Clean up expired entries
cleanupExpired :: forall k v. Ord k => Cache k v -> Effect Int
cleanupExpired cache = do
  now <- getCurrentTimeMs
  entries <- Ref.read cache.entries
  let expired = Map.filter (\entry -> entry.expiryTime <= now) entries
  let expiredKeys = Map.keys expired
  Ref.modify_ (\m -> foldl (\acc k -> Map.delete k acc) m expiredKeys) cache.entries
  pure (Map.size expired)

-- | Get cache size
size :: forall k v. Ord k => Cache k v -> Effect Int
size cache = do
  entries <- Ref.read cache.entries
  pure (Map.size entries)

-- | Check if key exists and is not expired
has :: forall k v. Ord k => Cache k v -> k -> Effect Boolean
has cache key = do
  result <- get cache key
  pure (isJust result)

-- | Get current time in milliseconds since epoch
foreign import getCurrentTimeMs :: Effect Number

-- | Helper to unwrap Milliseconds
unwrap :: Milliseconds -> Int
unwrap (Milliseconds ms) = ms
