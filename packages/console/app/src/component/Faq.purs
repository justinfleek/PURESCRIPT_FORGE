-- | FAQ Component
-- |
-- | Collapsible FAQ item.
-- | Pure data representation of FAQ state.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/component/faq.tsx
module Forge.Console.App.Component.Faq
  ( FaqItem
  , FaqState
  , FaqAction(..)
  , initialState
  , reduce
  , toggleItem
  ) where

import Prelude

import Data.Array as Array
import Data.Set (Set)
import Data.Set as Set

-- | FAQ item data
type FaqItem =
  { id :: String
  , question :: String
  , answer :: String
  }

-- | FAQ component state (tracks which items are expanded)
type FaqState =
  { expandedItems :: Set String
  }

-- | FAQ actions
data FaqAction
  = ToggleItem String
  | ExpandItem String
  | CollapseItem String
  | ExpandAll (Array String)
  | CollapseAll

derive instance eqFaqAction :: Eq FaqAction

-- | Initial FAQ state
initialState :: FaqState
initialState = { expandedItems: Set.empty }

-- | Reduce FAQ actions
reduce :: FaqAction -> FaqState -> FaqState
reduce action state = case action of
  ToggleItem id -> 
    if Set.member id state.expandedItems
      then state { expandedItems = Set.delete id state.expandedItems }
      else state { expandedItems = Set.insert id state.expandedItems }
  ExpandItem id -> 
    state { expandedItems = Set.insert id state.expandedItems }
  CollapseItem id -> 
    state { expandedItems = Set.delete id state.expandedItems }
  ExpandAll ids -> 
    state { expandedItems = Set.fromFoldable ids }
  CollapseAll -> 
    state { expandedItems = Set.empty }

-- | Check if an item is expanded
toggleItem :: String -> FaqState -> Boolean
toggleItem id state = Set.member id state.expandedItems
