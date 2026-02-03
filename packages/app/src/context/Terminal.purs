-- | Terminal context - manages terminal/PTY sessions
-- | Migrated from: forge-dev/packages/app/src/context/terminal.tsx
module App.Context.Terminal
  ( LocalPTY
  , TerminalStore
  , mkTerminalStore
  , getAllTerminals
  , getActiveTerminal
  , setActiveTerminal
  , addTerminal
  , updateTerminal
  , removeTerminal
  , moveTerminal
  , nextTerminal
  , previousTerminal
  , maxTerminalSessions
  ) where

import Prelude

import Data.Array (filter, findIndex, length, snoc, (!!))
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)

-- | Local PTY state
type LocalPTY =
  { id :: String
  , title :: String
  , titleNumber :: Int
  , rows :: Maybe Int
  , cols :: Maybe Int
  , buffer :: Maybe String
  , scrollY :: Maybe Int
  }

-- | Terminal store state
type TerminalStore =
  { active :: Maybe String
  , all :: Array LocalPTY
  }

-- | Maximum terminal sessions to cache
maxTerminalSessions :: Int
maxTerminalSessions = 20

-- | Create initial terminal store
mkTerminalStore :: TerminalStore
mkTerminalStore =
  { active: Nothing
  , all: []
  }

-- | Get all terminals
getAllTerminals :: TerminalStore -> Array LocalPTY
getAllTerminals = _.all

-- | Get active terminal ID
getActiveTerminal :: TerminalStore -> Maybe String
getActiveTerminal = _.active

-- | Set active terminal
setActiveTerminal :: String -> TerminalStore -> TerminalStore
setActiveTerminal id store =
  store { active = Just id }

-- | Add a new terminal
addTerminal :: LocalPTY -> TerminalStore -> TerminalStore
addTerminal pty store =
  store 
    { all = snoc store.all pty
    , active = Just pty.id
    }

-- | Update a terminal
updateTerminal :: LocalPTY -> TerminalStore -> TerminalStore
updateTerminal pty store =
  let
    updated = map (\t -> if t.id == pty.id then pty else t) store.all
  in
    store { all = updated }

-- | Remove a terminal
removeTerminal :: String -> TerminalStore -> TerminalStore
removeTerminal id store =
  let
    filtered = filter (\t -> t.id /= id) store.all
    newActive =
      if store.active == Just id
      then
        case Array.head filtered of
          Nothing -> Nothing
          Just t -> Just t.id
      else store.active
  in
    store { all = filtered, active = newActive }

-- | Move terminal to a new index
moveTerminal :: String -> Int -> TerminalStore -> TerminalStore
moveTerminal id toIndex store =
  case findIndex (\t -> t.id == id) store.all of
    Nothing -> store
    Just fromIndex ->
      let
        item = store.all !! fromIndex
      in
        case item of
          Nothing -> store
          Just pty ->
            let
              removed = removeAtIndex fromIndex store.all
              inserted = insertAtIndex toIndex pty removed
            in
              store { all = inserted }
  where
    removeAtIndex :: forall a. Int -> Array a -> Array a
    removeAtIndex idx arr =
      case splitAt idx arr of
        { before, after: _ : rest } -> before <> rest
        _ -> arr
    
    insertAtIndex :: forall a. Int -> a -> Array a -> Array a
    insertAtIndex idx item arr =
      let { before, after } = splitAt idx arr
      in before <> [item] <> after
    
    splitAt :: forall a. Int -> Array a -> { before :: Array a, after :: Array a }
    splitAt n arr = { before: Array.take n arr, after: Array.drop n arr }

-- | Switch to next terminal
nextTerminal :: TerminalStore -> TerminalStore
nextTerminal store =
  case store.active of
    Nothing -> store
    Just activeId ->
      case findIndex (\t -> t.id == activeId) store.all of
        Nothing -> store
        Just idx ->
          let
            nextIdx = (idx + 1) `mod` length store.all
          in
            case store.all !! nextIdx of
              Nothing -> store
              Just t -> store { active = Just t.id }

-- | Switch to previous terminal
previousTerminal :: TerminalStore -> TerminalStore
previousTerminal store =
  case store.active of
    Nothing -> store
    Just activeId ->
      case findIndex (\t -> t.id == activeId) store.all of
        Nothing -> store
        Just idx ->
          let
            len = length store.all
            prevIdx = if idx == 0 then len - 1 else idx - 1
          in
            case store.all !! prevIdx of
              Nothing -> store
              Just t -> store { active = Just t.id }
