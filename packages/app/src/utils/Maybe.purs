-- | Maybe/Option type utilities
-- | Migrated from: forge-dev/packages/app/src/utils/maybe.ts (67 lines)
-- |
-- | Note: This module provides TypeScript-compatible Maybe operations.
-- | In PureScript, we typically use Data.Maybe directly, but this
-- | provides the same API as the TypeScript version for consistency.
module Sidepanel.Utils.Maybe
  ( Maybe'(..)
  , just'
  , none'
  , isJust'
  , isNone'
  , fromMaybe'
  , mapMaybe'
  , bindMaybe'
  -- Re-exports for convenience
  , module Data.Maybe
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, isJust, isNothing)

-- | TypeScript-compatible Maybe type
-- | Uses tagged union pattern matching the TypeScript interface
data Maybe' a
  = Just' a
  | None'

derive instance eqMaybe' :: Eq a => Eq (Maybe' a)
derive instance functorMaybe' :: Functor Maybe'

-- | Create a Maybe' containing a value
just' :: forall a. a -> Maybe' a
just' = Just'

-- | Create an empty Maybe'
none' :: forall a. Maybe' a
none' = None'

-- | Check if Maybe' contains a value
isJust' :: forall a. Maybe' a -> Boolean
isJust' (Just' _) = true
isJust' None' = false

-- | Check if Maybe' is empty
isNone' :: forall a. Maybe' a -> Boolean
isNone' None' = true
isNone' (Just' _) = false

-- | Extract value with fallback
fromMaybe' :: forall a. a -> Maybe' a -> a
fromMaybe' defaultValue maybe' = case maybe' of
  Just' value -> value
  None' -> defaultValue

-- | Map over Maybe' value
mapMaybe' :: forall a b. (a -> b) -> Maybe' a -> Maybe' b
mapMaybe' f = case _ of
  Just' value -> Just' (f value)
  None' -> None'

-- | Chain Maybe' operations (flatMap/bind)
bindMaybe' :: forall a b. Maybe' a -> (a -> Maybe' b) -> Maybe' b
bindMaybe' maybe' f = case maybe' of
  Just' value -> f value
  None' -> None'

-- | Convert from standard Maybe to Maybe'
fromMaybe'' :: forall a. Maybe a -> Maybe' a
fromMaybe'' = case _ of
  Just x -> Just' x
  Nothing -> None'

-- | Convert from Maybe' to standard Maybe
toMaybe :: forall a. Maybe' a -> Maybe a
toMaybe = case _ of
  Just' x -> Just x
  None' -> Nothing

-- | Applicative instance for Maybe'
instance applyMaybe' :: Apply Maybe' where
  apply (Just' f) (Just' x) = Just' (f x)
  apply _ _ = None'

instance applicativeMaybe' :: Applicative Maybe' where
  pure = Just'

instance bindMaybe'' :: Bind Maybe' where
  bind = bindMaybe'

instance monadMaybe' :: Monad Maybe'
