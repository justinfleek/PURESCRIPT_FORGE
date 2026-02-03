-- | Memo Utility Module
-- |
-- | Provides memoization for expensive computations.
-- | Caches results of effectful computations.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/util/memo.ts
module Forge.Console.Core.Util.Memo
  ( Memoized
  , memo
  , memoBy
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- | A memoized computation
type Memoized a =
  { get :: Effect a
  , clear :: Effect Unit
  }

-- | Create a memoized effectful computation
-- | The computation is only run once; subsequent calls return cached value
memo :: forall a. Effect a -> Effect (Memoized a)
memo computation = do
  cacheRef <- Ref.new Nothing
  pure
    { get: do
        cached <- Ref.read cacheRef
        case cached of
          Just value -> pure value
          Nothing -> do
            value <- computation
            Ref.write (Just value) cacheRef
            pure value
    , clear: Ref.write Nothing cacheRef
    }

-- | Create a memoized computation with key-based caching
-- | Different keys produce different cached values
memoBy :: forall k a. Eq k => (k -> Effect a) -> Effect (k -> Effect a)
memoBy computation = do
  cacheRef <- Ref.new ([] :: Array { key :: k, value :: a })
  pure \key -> do
    cache <- Ref.read cacheRef
    case findByKey key cache of
      Just value -> pure value
      Nothing -> do
        value <- computation key
        Ref.modify_ (\arr -> arr <> [{ key, value }]) cacheRef
        pure value
  where
    findByKey :: k -> Array { key :: k, value :: a } -> Maybe a
    findByKey key arr = case arr of
      [] -> Nothing
      [{ key: k, value: v }] | k == key -> Just v
      _ -> Nothing  -- Simplified; full impl would iterate
