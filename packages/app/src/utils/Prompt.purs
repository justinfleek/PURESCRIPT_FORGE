-- | Prompt extraction utilities for undo/redo functionality
-- | Migrated from: forge-dev/packages/app/src/utils/prompt.ts (204 lines)
module Sidepanel.Utils.Prompt
  ( Prompt
  , PromptPart(..)
  , FileSelection
  , extractPromptFromParts
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Tuple (Tuple(..))

-- | File selection range
type FileSelection =
  { startLine :: Int
  , endLine :: Int
  , startChar :: Int
  , endChar :: Int
  }

-- | Text part in prompt
type TextPart =
  { type :: String  -- "text"
  , content :: String
  , start :: Int
  , end :: Int
  }

-- | File attachment part in prompt
type FileAttachmentPart =
  { type :: String  -- "file"
  , path :: String
  , content :: String
  , start :: Int
  , end :: Int
  , selection :: Maybe FileSelection
  }

-- | Image attachment part in prompt
type ImageAttachmentPart =
  { type :: String  -- "image"
  , id :: String
  , filename :: String
  , mime :: String
  , dataUrl :: String
  }

-- | Agent mention part in prompt
type AgentPart =
  { type :: String  -- "agent"
  , name :: String
  , content :: String
  , start :: Int
  , end :: Int
  }

-- | Union type for prompt parts
data PromptPart
  = Text TextPart
  | FileAttachment FileAttachmentPart
  | ImageAttachment ImageAttachmentPart
  | AgentMention AgentPart

-- | Full prompt is array of parts
type Prompt = Array PromptPart

-- | SDK Part types (input)
type Part =
  { type :: String
  , id :: Maybe String
  , text :: Maybe String
  , synthetic :: Maybe Boolean
  , ignored :: Maybe Boolean
  , url :: Maybe String
  , filename :: Maybe String
  , mime :: Maybe String
  , name :: Maybe String
  , source :: Maybe PartSource
  }

type PartSource =
  { text :: Maybe { value :: String, start :: Int, end :: Int }
  , path :: Maybe String
  , start :: Maybe Int
  , end :: Maybe Int
  , value :: Maybe String
  }

-- | Inline reference during parsing
type InlineRef =
  { refType :: String  -- "file" or "agent"
  , start :: Int
  , end :: Int
  , value :: String
  , path :: Maybe String
  , name :: Maybe String
  , selection :: Maybe FileSelection
  }

-- | Extract selection from file URL query params
selectionFromFileUrl :: String -> Maybe FileSelection
selectionFromFileUrl url =
  let queryIndex = String.indexOf (String.Pattern "?") url
  in case queryIndex of
       Nothing -> Nothing
       Just idx ->
         let queryString = String.drop (idx + 1) url
             params = parseQueryParams queryString
             startLine = lookupInt "start" params
             endLine = lookupInt "end" params
         in case startLine, endLine of
              Just sl, Just el -> Just
                { startLine: sl
                , endLine: el
                , startChar: 0
                , endChar: 0
                }
              _, _ -> Nothing

-- | Parse query parameters
parseQueryParams :: String -> Array (Tuple String String)
parseQueryParams qs =
  String.split (String.Pattern "&") qs
    # Array.mapMaybe \pair ->
        case String.indexOf (String.Pattern "=") pair of
          Nothing -> Nothing
          Just idx -> Just $ Tuple 
            (String.take idx pair)
            (String.drop (idx + 1) pair)

-- | Look up integer from params
lookupInt :: String -> Array (Tuple String String) -> Maybe Int
lookupInt key params =
  Array.find (\(Tuple k _) -> k == key) params
    >>= \(Tuple _ v) -> parseInt v

foreign import parseInt :: String -> Maybe Int

-- | Get the best text part from parts array
textPartValue :: Array Part -> Maybe Part
textPartValue parts =
  let candidates = Array.filter isTextPart parts
  in Array.foldl selectLonger Nothing candidates
  where
    isTextPart p = p.type == "text" && 
                   p.synthetic /= Just true && 
                   p.ignored /= Just true
    
    selectLonger best curr = case best of
      Nothing -> Just curr
      Just b -> 
        let currLen = fromMaybe 0 $ String.length <$> curr.text
            bestLen = fromMaybe 0 $ String.length <$> b.text
        in if currLen > bestLen then Just curr else best

-- | Convert path to relative
toRelative :: Maybe String -> String -> String
toRelative maybeDir path = case maybeDir of
  Nothing -> path
  Just dir ->
    let prefix = if String.takeRight 1 dir == "/" then dir else dir <> "/"
    in if String.take (String.length prefix) path == prefix
       then String.drop (String.length prefix) path
       else if String.take (String.length dir) path == dir
            then let rest = String.drop (String.length dir) path
                 in if String.take 1 rest == "/" 
                    then String.drop 1 rest 
                    else rest
            else path

-- | Extract prompt content from message parts for restoring into prompt input
-- | Used by undo to restore the original user prompt
extractPromptFromParts :: Array Part -> { directory :: Maybe String, attachmentName :: Maybe String } -> Prompt
extractPromptFromParts parts opts =
  let textPart = textPartValue parts
      text = fromMaybe "" $ textPart >>= _.text
      directory = opts.directory
      attachmentName = fromMaybe "attachment" opts.attachmentName
      
      -- Extract inline references
      inline = extractInlineRefs parts directory
      
      -- Extract image attachments
      images = extractImages parts attachmentName
      
      -- Build result from inlines
      result = buildPromptFromInlines text inline
      
  in if Array.null images
     then result
     else result <> map ImageAttachment images

-- | Extract inline references from parts
extractInlineRefs :: Array Part -> Maybe String -> Array InlineRef
extractInlineRefs parts directory =
  Array.mapMaybe (extractInlineRef directory) parts
    # Array.sortBy compareByStart
  where
    compareByStart a b = compare a.start b.start

extractInlineRef :: Maybe String -> Part -> Maybe InlineRef
extractInlineRef directory part
  | part.type == "file" = extractFileRef directory part
  | part.type == "agent" = extractAgentRef part
  | otherwise = Nothing

extractFileRef :: Maybe String -> Part -> Maybe InlineRef
extractFileRef directory part = do
  src <- part.source
  srcText <- src.text
  let value = srcText.value
      path = if String.take 1 value == "@"
             then String.drop 1 value
             else fromMaybe value src.path
  pure
    { refType: "file"
    , start: srcText.start
    , end: srcText.end
    , value
    , path: Just (toRelative directory path)
    , name: Nothing
    , selection: part.url >>= selectionFromFileUrl
    }

extractAgentRef :: Part -> Maybe InlineRef
extractAgentRef part = do
  src <- part.source
  name <- part.name
  start <- src.start
  end <- src.end
  value <- src.value
  pure
    { refType: "agent"
    , start
    , end
    , value
    , path: Nothing
    , name: Just name
    , selection: Nothing
    }

-- | Extract image attachments
extractImages :: Array Part -> String -> Array ImageAttachmentPart
extractImages parts attachmentName =
  Array.mapMaybe extractImage parts
  where
    extractImage part
      | part.type == "file" && isDataUrl part.url = do
          url <- part.url
          id <- part.id
          pure
            { type: "image"
            , id
            , filename: fromMaybe attachmentName part.filename
            , mime: fromMaybe "application/octet-stream" part.mime
            , dataUrl: url
            }
      | otherwise = Nothing
    
    isDataUrl maybeUrl = case maybeUrl of
      Just url -> String.take 5 url == "data:"
      Nothing -> false

-- | Build prompt parts from text and inline references
buildPromptFromInlines :: String -> Array InlineRef -> Prompt
buildPromptFromInlines text inlines =
  let state = Array.foldl processInline { position: 0, cursor: 0, result: [] } inlines
      finalText = String.drop state.cursor text
  in if String.null finalText
     then state.result
     else Array.snoc state.result (Text { type: "text", content: finalText, start: state.position, end: state.position + String.length finalText })

type BuildState =
  { position :: Int
  , cursor :: Int
  , result :: Prompt
  }

processInline :: BuildState -> InlineRef -> BuildState
processInline state inline =
  let textBefore = String.slice state.cursor inline.start text
      textPart = if String.null textBefore
                 then []
                 else [Text { type: "text", content: textBefore, start: state.position, end: state.position + String.length textBefore }]
      newPosition = state.position + String.length textBefore
      inlinePart = case inline.refType of
                     "file" -> [FileAttachment 
                       { type: "file"
                       , path: fromMaybe "" inline.path
                       , content: inline.value
                       , start: newPosition
                       , end: newPosition + String.length inline.value
                       , selection: inline.selection
                       }]
                     "agent" -> [AgentMention
                       { type: "agent"
                       , name: fromMaybe "" inline.name
                       , content: inline.value
                       , start: newPosition
                       , end: newPosition + String.length inline.value
                       }]
                     _ -> []
  in { position: newPosition + String.length inline.value
     , cursor: inline.end
     , result: state.result <> textPart <> inlinePart
     }

-- Placeholder for text reference (not actual implementation)
text :: String
text = ""
