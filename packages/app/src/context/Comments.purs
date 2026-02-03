-- | Comments context - manages line comments on files
-- | Migrated from: forge-dev/packages/app/src/context/comments.tsx
module App.Context.Comments
  ( LineComment
  , SelectedLineRange
  , CommentFocus
  , CommentsStore
  , mkCommentsStore
  , listComments
  , allComments
  , addComment
  , removeComment
  , setFocus
  , clearFocus
  , setActive
  , clearActive
  ) where

import Prelude

import Data.Array (filter, sortBy, (:), snoc)
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ordering (Ordering)
import Effect.Random (randomInt)

-- | Selected line range
type SelectedLineRange =
  { start :: Int
  , end :: Int
  , side :: Maybe String  -- "additions" | "deletions"
  , endSide :: Maybe String
  }

-- | Line comment
type LineComment =
  { id :: String
  , file :: String
  , selection :: SelectedLineRange
  , comment :: String
  , time :: Number
  }

-- | Comment focus state
type CommentFocus =
  { file :: String
  , id :: String
  }

-- | Comments store state
type CommentsStore =
  { comments :: Map String (Array LineComment)  -- file -> comments
  , focus :: Maybe CommentFocus
  , active :: Maybe CommentFocus
  }

-- | Create initial comments store
mkCommentsStore :: CommentsStore
mkCommentsStore =
  { comments: Map.empty
  , focus: Nothing
  , active: Nothing
  }

-- | List comments for a file
listComments :: String -> CommentsStore -> Array LineComment
listComments file store =
  fromMaybe [] (Map.lookup file store.comments)

-- | Get all comments sorted by time
allComments :: CommentsStore -> Array LineComment
allComments store =
  let
    allFiles = Map.values store.comments
    flattened = foldl (\acc arr -> acc <> arr) [] allFiles
  in
    sortBy compareByTime flattened
  where
    compareByTime :: LineComment -> LineComment -> Ordering
    compareByTime a b = compare a.time b.time

-- | Add a comment
addComment :: { file :: String, selection :: SelectedLineRange, comment :: String } -> String -> Number -> CommentsStore -> CommentsStore
addComment input id time store =
  let
    newComment =
      { id
      , file: input.file
      , selection: input.selection
      , comment: input.comment
      , time
      }
    
    existing = fromMaybe [] (Map.lookup input.file store.comments)
    updated = snoc existing newComment
    newComments = Map.insert input.file updated store.comments
    newFocus = Just { file: input.file, id }
  in
    store { comments = newComments, focus = newFocus }

-- | Remove a comment
removeComment :: String -> String -> CommentsStore -> CommentsStore
removeComment file id store =
  let
    existing = fromMaybe [] (Map.lookup file store.comments)
    updated = filter (\c -> c.id /= id) existing
    newComments = Map.insert file updated store.comments
    
    -- Clear focus if this comment was focused
    newFocus = case store.focus of
      Just f | f.id == id -> Nothing
      other -> other
  in
    store { comments = newComments, focus = newFocus }

-- | Set focus
setFocus :: Maybe CommentFocus -> CommentsStore -> CommentsStore
setFocus focus store = store { focus = focus }

-- | Clear focus
clearFocus :: CommentsStore -> CommentsStore
clearFocus store = store { focus = Nothing }

-- | Set active
setActive :: Maybe CommentFocus -> CommentsStore -> CommentsStore
setActive active store = store { active = active }

-- | Clear active
clearActive :: CommentsStore -> CommentsStore
clearActive store = store { active = Nothing }
