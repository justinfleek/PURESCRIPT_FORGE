-- | Prompt context - manages prompt input state
-- | Migrated from: forge-dev/packages/app/src/context/prompt.tsx
module App.Context.Prompt
  ( TextPart
  , FileAttachmentPart
  , AgentPart
  , ImageAttachmentPart
  , ContentPart(..)
  , Prompt
  , FileSelection
  , FileContextItem
  , ContextItem(..)
  , PromptStore
  , defaultPrompt
  , mkPromptStore
  , isPromptEqual
  , isSelectionEqual
  , contextItemKey
  , addContextItem
  , removeContextItem
  , setPrompt
  , resetPrompt
  ) where

import Prelude

import Data.Array (filter, length, snoc, (:))
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (take) as String

-- | File selection range
type FileSelection =
  { startLine :: Int
  , startChar :: Int
  , endLine :: Int
  , endChar :: Int
  }

-- | Text part of a prompt
type TextPart =
  { content :: String
  , start :: Int
  , end :: Int
  }

-- | File attachment part
type FileAttachmentPart =
  { content :: String
  , start :: Int
  , end :: Int
  , path :: String
  , selection :: Maybe FileSelection
  }

-- | Agent part
type AgentPart =
  { content :: String
  , start :: Int
  , end :: Int
  , name :: String
  }

-- | Image attachment part
type ImageAttachmentPart =
  { id :: String
  , filename :: String
  , mime :: String
  , dataUrl :: String
  }

-- | Content part discriminated union
data ContentPart
  = TextContent TextPart
  | FileContent FileAttachmentPart
  | AgentContent AgentPart
  | ImageContent ImageAttachmentPart

-- | Prompt is an array of content parts
type Prompt = Array ContentPart

-- | File context item
type FileContextItem =
  { path :: String
  , selection :: Maybe FileSelection
  , comment :: Maybe String
  , commentID :: Maybe String
  , commentOrigin :: Maybe String  -- "review" | "file"
  , preview :: Maybe String
  }

-- | Context item (currently only file type)
data ContextItem
  = FileContext FileContextItem

-- | Context item with key for deduplication
type KeyedContextItem =
  { key :: String
  , item :: ContextItem
  }

-- | Prompt store state
type PromptStore =
  { prompt :: Prompt
  , cursor :: Maybe Int
  , context :: Array KeyedContextItem
  }

-- | Default prompt (empty text)
defaultPrompt :: Prompt
defaultPrompt = [ TextContent { content: "", start: 0, end: 0 } ]

-- | Create initial prompt store
mkPromptStore :: PromptStore
mkPromptStore =
  { prompt: defaultPrompt
  , cursor: Nothing
  , context: []
  }

-- | Check if two file selections are equal
isSelectionEqual :: Maybe FileSelection -> Maybe FileSelection -> Boolean
isSelectionEqual Nothing Nothing = true
isSelectionEqual Nothing (Just _) = false
isSelectionEqual (Just _) Nothing = false
isSelectionEqual (Just a) (Just b) =
  a.startLine == b.startLine &&
  a.startChar == b.startChar &&
  a.endLine == b.endLine &&
  a.endChar == b.endChar

-- | Check if two prompts are equal
isPromptEqual :: Prompt -> Prompt -> Boolean
isPromptEqual a b =
  if length a /= length b
  then false
  else checkParts a b
  where
    checkParts :: Prompt -> Prompt -> Boolean
    checkParts [] [] = true
    checkParts [] _ = false
    checkParts _ [] = false
    checkParts (x : xs) (y : ys) = partEqual x y && checkParts xs ys
    
    partEqual :: ContentPart -> ContentPart -> Boolean
    partEqual (TextContent ta) (TextContent tb) = ta.content == tb.content
    partEqual (FileContent fa) (FileContent fb) = 
      fa.path == fb.path && isSelectionEqual fa.selection fb.selection
    partEqual (AgentContent aa) (AgentContent ab) = aa.name == ab.name
    partEqual (ImageContent ia) (ImageContent ib) = ia.id == ib.id
    partEqual _ _ = false

-- | Generate key for a context item
contextItemKey :: ContextItem -> String
contextItemKey (FileContext item) =
  let
    start = case item.selection of
      Nothing -> ""
      Just s -> show s.startLine
    end = case item.selection of
      Nothing -> ""
      Just s -> show s.endLine
    baseKey = "file:" <> item.path <> ":" <> start <> ":" <> end
  in
    case item.commentID of
      Just cid -> baseKey <> ":c=" <> cid
      Nothing ->
        case item.comment of
          Nothing -> baseKey
          Just c ->
            let
              trimmed = String.take 8 c
            in
              baseKey <> ":c=" <> trimmed

-- | Add context item (if not already present)
addContextItem :: ContextItem -> PromptStore -> PromptStore
addContextItem item store =
  let
    key = contextItemKey item
    exists = Array.any (\x -> x.key == key) store.context
  in
    if exists
    then store
    else store { context = snoc store.context { key, item } }

-- | Remove context item by key
removeContextItem :: String -> PromptStore -> PromptStore
removeContextItem key store =
  store { context = filter (\x -> x.key /= key) store.context }

-- | Set prompt
setPrompt :: Prompt -> Maybe Int -> PromptStore -> PromptStore
setPrompt prompt cursor store =
  store { prompt = prompt, cursor = cursor }

-- | Reset prompt to default
resetPrompt :: PromptStore -> PromptStore
resetPrompt store =
  store { prompt = defaultPrompt, cursor = Just 0 }
