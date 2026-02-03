-- | Filtered List Hook - Fuzzy Search and Navigation
-- |
-- | Provides a filtered list with:
-- | - Fuzzy search using fuzzysort
-- | - Keyboard navigation (arrow keys, ctrl+n/p)
-- | - Grouping and sorting
-- | - Active item tracking
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/hooks/use-filtered-list.tsx
module Forge.UI.Hooks.UseFilteredList
  ( FilteredListProps
  , FilteredListState
  , useFilteredList
  , GroupedItems
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Web.Event.Event (Event)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)

-- | A group of items with a category label
type GroupedItems a =
  { category :: String
  , items :: Array a
  }

-- | Props for the filtered list hook
type FilteredListProps a =
  { items :: Array a  -- Can also be a function (filter -> items)
  , key :: a -> String
  , filterKeys :: Maybe (Array String)
  , current :: Maybe a
  , groupBy :: Maybe (a -> String)
  , sortBy :: Maybe (a -> a -> Ordering)
  , sortGroupsBy :: Maybe (GroupedItems a -> GroupedItems a -> Ordering)
  , onSelect :: Maybe (a -> Int -> Effect Unit)
  , noInitialSelection :: Boolean
  }

-- | State returned by the filtered list hook
type FilteredListState a =
  { grouped :: Effect (Array (GroupedItems a))
  , filter :: Effect String
  , flat :: Effect (Array a)
  , reset :: Effect Unit
  , refetch :: Effect Unit
  , clear :: Effect Unit
  , onKeyDown :: KeyboardEvent -> Effect Unit
  , onInput :: String -> Effect Unit
  , active :: Effect String
  , setActive :: String -> Effect Unit
  }

-- | Perform fuzzy search on items
foreign import fuzzySearch 
  :: forall a
   . Array a 
  -> String 
  -> Maybe (Array String) 
  -> Effect (Array a)

-- | Create a filtered list hook
useFilteredList 
  :: forall a
   . FilteredListProps a 
  -> Effect (FilteredListState a)
useFilteredList props = do
  filterRef <- Ref.new ""
  activeRef <- Ref.new ""
  cachedGroupedRef <- Ref.new ([] :: Array (GroupedItems a))
  
  let
    getFlat :: Effect (Array a)
    getFlat = do
      groups <- Ref.read cachedGroupedRef
      pure $ Array.concatMap _.items groups
    
    getInitialActive :: Effect String
    getInitialActive = do
      if props.noInitialSelection
        then pure ""
        else case props.current of
          Just c -> pure (props.key c)
          Nothing -> do
            items <- getFlat
            case Array.head items of
              Just first -> pure (props.key first)
              Nothing -> pure ""
    
    updateGrouped :: Effect Unit
    updateGrouped = do
      filterStr <- Ref.read filterRef
      filtered <- fuzzySearch props.items filterStr props.filterKeys
      
      let
        -- Group items
        grouped = case props.groupBy of
          Nothing -> [{ category: "", items: filtered }]
          Just groupFn -> groupItemsBy groupFn filtered
        
        -- Sort items within groups
        sortedGroups = case props.sortBy of
          Nothing -> grouped
          Just sortFn -> map (\g -> g { items = Array.sortBy sortFn g.items }) grouped
        
        -- Sort groups
        finalGroups = case props.sortGroupsBy of
          Nothing -> sortedGroups
          Just sortFn -> Array.sortBy sortFn sortedGroups
      
      Ref.write finalGroups cachedGroupedRef
    
    reset :: Effect Unit
    reset = do
      if props.noInitialSelection
        then Ref.write "" activeRef
        else do
          items <- getFlat
          case Array.head items of
            Just first -> Ref.write (props.key first) activeRef
            Nothing -> pure unit
    
    handleKeyDown :: KeyboardEvent -> Effect Unit
    handleKeyDown event = do
      key <- getEventKey event
      case key of
        "Enter" -> do
          activeKey <- Ref.read activeRef
          items <- getFlat
          let mSelected = Array.findIndex (\x -> props.key x == activeKey) items
          case mSelected of
            Just idx -> case Array.index items idx of
              Just item -> case props.onSelect of
                Just onSelect -> onSelect item idx
                Nothing -> pure unit
              Nothing -> pure unit
            Nothing -> pure unit
        "ArrowDown" -> moveActive 1
        "ArrowUp" -> moveActive (-1)
        _ -> pure unit
    
    moveActive :: Int -> Effect Unit
    moveActive delta = do
      items <- getFlat
      activeKey <- Ref.read activeRef
      let 
        currentIdx = fromMaybe 0 $ Array.findIndex (\x -> props.key x == activeKey) items
        newIdx = (currentIdx + delta) `mod` Array.length items
      case Array.index items (if newIdx < 0 then Array.length items - 1 else newIdx) of
        Just item -> Ref.write (props.key item) activeRef
        Nothing -> pure unit
    
    onInput :: String -> Effect Unit
    onInput value = do
      Ref.write value filterRef
      updateGrouped
      reset

  -- Initial update
  updateGrouped
  initialActive <- getInitialActive
  Ref.write initialActive activeRef

  pure
    { grouped: Ref.read cachedGroupedRef
    , filter: Ref.read filterRef
    , flat: getFlat
    , reset
    , refetch: updateGrouped
    , clear: do
        Ref.write "" filterRef
        updateGrouped
    , onKeyDown: handleKeyDown
    , onInput
    , active: Ref.read activeRef
    , setActive: \key -> Ref.write key activeRef
    }

-- | Group items by a key function
groupItemsBy :: forall a. (a -> String) -> Array a -> Array (GroupedItems a)
groupItemsBy keyFn items =
  let
    addToGroup :: Array (GroupedItems a) -> a -> Array (GroupedItems a)
    addToGroup groups item =
      let key = keyFn item
      in case Array.findIndex (\g -> g.category == key) groups of
        Just idx -> 
          case Array.modifyAt idx (\g -> g { items = Array.snoc g.items item }) groups of
            Just updated -> updated
            Nothing -> groups
        Nothing -> Array.snoc groups { category: key, items: [item] }
  in Array.foldl addToGroup [] items

-- | Get key from keyboard event
foreign import getEventKey :: KeyboardEvent -> Effect String
