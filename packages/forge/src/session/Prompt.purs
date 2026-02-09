-- | Session Prompt - handle user prompts
-- | Ported from: opencode-dev/packages/opencode/src/session/prompt.ts
module Forge.Session.Prompt 
  ( -- * Types
    PromptRequest
  , PromptResult
  , PromptPartType(..)
  , PromptPart
  , FileSelection
  , ContentPart(..)
  , Prompt
  , PromptStore
  , ImageAttachmentPart
  , FileAttachmentPart
    -- * Core Functions
  , sendPrompt
  , executeCommand
  , cancelPrompt
    -- * Prompt Store
  , mkPromptStore
  , defaultPrompt
  , setPrompt
  , resetPrompt
  , isPromptEqual
    -- * Content Parts
  , extractText
  , hasFiles
  , hasImages
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | File selection range (1-based line/column numbers)
type FileSelection =
  { startLine :: Int
  , startChar :: Int
  , endLine :: Int
  , endChar :: Int
  }

-- | Prompt part types
data PromptPartType
  = TextPart
  | FilePart
  | ImagePart
  | AgentPart

derive instance eqPromptPartType :: Eq PromptPartType

instance showPromptPartType :: Show PromptPartType where
  show TextPart = "text"
  show FilePart = "file"
  show ImagePart = "image"
  show AgentPart = "agent"

-- | Generic prompt part
type PromptPart =
  { partType :: PromptPartType
  , content :: String
  , start :: Int
  , end :: Int
  }

-- | Text content part
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

-- | Agent mention part
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

derive instance eqContentPart :: Eq ContentPart

-- | Prompt is an array of content parts
type Prompt = Array ContentPart

-- | Prompt request to send to LLM
type PromptRequest =
  { sessionId :: String
  , text :: String
  , files :: Array String
  , images :: Array ImageAttachmentPart
  , model :: Maybe String
  , agent :: Maybe String
  , systemPrompt :: Maybe String
  }

-- | Prompt result from LLM
type PromptResult =
  { messageId :: String
  , content :: String
  , toolCalls :: Array ToolCall
  , usage :: TokenUsage
  }

-- | Tool call from LLM response
type ToolCall =
  { id :: String
  , name :: String
  , arguments :: String
  }

-- | Token usage from LLM response
type TokenUsage =
  { input :: Int
  , output :: Int
  , reasoning :: Int
  }

-- | Prompt store state for UI
type PromptStore =
  { prompt :: Prompt
  , cursor :: Maybe Int
  , context :: Array ContextItem
  , isSubmitting :: Boolean
  , error :: Maybe String
  }

-- | Context item for additional context
type ContextItem =
  { key :: String
  , itemType :: String
  , path :: Maybe String
  , content :: Maybe String
  }

-- ============================================================================
-- CORE FUNCTIONS
-- ============================================================================

-- | Send a prompt to a session
sendPrompt :: PromptRequest -> Aff (Either String PromptResult)
sendPrompt request = do
  -- Validate request
  if String.null request.text && Array.null request.files then
    pure $ Left "Prompt must contain text or files"
  else do
    -- Execute prompt via FFI
    result <- sendPromptFFI request
    pure result

-- | FFI for sending prompt
foreign import sendPromptFFI :: PromptRequest -> Aff (Either String PromptResult)

-- | Execute a command in a session (slash commands)
executeCommand :: String -> String -> String -> Aff (Either String Unit)
executeCommand sessionId command args = do
  result <- executeCommandFFI sessionId command args
  pure result

-- | FFI for executing command
foreign import executeCommandFFI :: String -> String -> String -> Aff (Either String Unit)

-- | Cancel an ongoing prompt
cancelPrompt :: String -> Aff (Either String Unit)
cancelPrompt sessionId = do
  result <- cancelPromptFFI sessionId
  pure result

-- | FFI for cancelling prompt
foreign import cancelPromptFFI :: String -> Aff (Either String Unit)

-- ============================================================================
-- PROMPT STORE
-- ============================================================================

-- | Default prompt (empty text)
defaultPrompt :: Prompt
defaultPrompt = [ TextContent { content: "", start: 0, end: 0 } ]

-- | Create initial prompt store
mkPromptStore :: PromptStore
mkPromptStore =
  { prompt: defaultPrompt
  , cursor: Nothing
  , context: []
  , isSubmitting: false
  , error: Nothing
  }

-- | Set prompt
setPrompt :: Prompt -> Maybe Int -> PromptStore -> PromptStore
setPrompt prompt cursor store =
  store { prompt = prompt, cursor = cursor }

-- | Reset prompt to default
resetPrompt :: PromptStore -> PromptStore
resetPrompt store =
  store { prompt = defaultPrompt, cursor = Just 0, error = Nothing }

-- | Check if two prompts are equal
isPromptEqual :: Prompt -> Prompt -> Boolean
isPromptEqual a b =
  if Array.length a /= Array.length b
  then false
  else Array.all identity (Array.zipWith partEqual a b)
  where
    partEqual :: ContentPart -> ContentPart -> Boolean
    partEqual (TextContent ta) (TextContent tb) = ta.content == tb.content
    partEqual (FileContent fa) (FileContent fb) = 
      fa.path == fb.path && isSelectionEqual fa.selection fb.selection
    partEqual (AgentContent aa) (AgentContent ab) = aa.name == ab.name
    partEqual (ImageContent ia) (ImageContent ib) = ia.id == ib.id
    partEqual _ _ = false

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

-- ============================================================================
-- CONTENT HELPERS
-- ============================================================================

-- | Extract all text content from prompt
extractText :: Prompt -> String
extractText parts =
  String.joinWith "" $ Array.mapMaybe getText parts
  where
    getText (TextContent t) = Just t.content
    getText _ = Nothing

-- | Check if prompt has file attachments
hasFiles :: Prompt -> Boolean
hasFiles parts = Array.any isFile parts
  where
    isFile (FileContent _) = true
    isFile _ = false

-- | Check if prompt has image attachments
hasImages :: Prompt -> Boolean
hasImages parts = Array.any isImage parts
  where
    isImage (ImageContent _) = true
    isImage _ = false
