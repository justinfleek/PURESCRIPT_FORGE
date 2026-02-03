-- | MessagePart Types Module
-- | Shared types for message part rendering system.
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/message-part.tsx
-- | This module contains type definitions extracted from the original 1577-line file.

module UI.Components.MessagePart.Types
  ( Message
  , UserMessage
  , AssistantMessage
  , Part(..)
  , TextPartData
  , ToolPartData
  , ToolState
  , ReasoningPartData
  , FilePartData
  , AgentPartData
  , Diagnostic
  , Todo
  , QuestionInfo
  , QuestionAnswer
  , QuestionOption
  , ToolInfo
  , MessageProps
  , MessagePartProps
  , ToolProps
  , PermissionRequest
  , PermissionResponse(..)
  , partType
  ) where

import Prelude

import Data.Maybe (Maybe)
import Foreign.Object (Object)

-- ═══════════════════════════════════════════════════════════════════════════════
-- MESSAGE TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base message type
type Message =
  { id :: String
  , role :: String  -- "user" | "assistant"
  , sessionID :: String
  , parentID :: Maybe String
  , time :: { created :: Number, completed :: Maybe Number }
  , error :: Maybe { data :: Maybe { message :: Maybe String } }
  , summary :: Maybe { title :: Maybe String, diffs :: Array FileDiff }
  }

-- | File diff from summary
type FileDiff =
  { file :: String
  , before :: Maybe String
  , after :: Maybe String
  , additions :: Int
  , deletions :: Int
  }

type UserMessage = Message
type AssistantMessage = Message

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Part sum type
data Part
  = TextPart TextPartData
  | ToolPart ToolPartData
  | ReasoningPart ReasoningPartData
  | FilePart FilePartData
  | AgentPart AgentPartData

derive instance eqPart :: Eq Part

-- | Get part type string
partType :: Part -> String
partType (TextPart _) = "text"
partType (ToolPart _) = "tool"
partType (ReasoningPart _) = "reasoning"
partType (FilePart _) = "file"
partType (AgentPart _) = "agent"

-- | Text part data
type TextPartData =
  { id :: String
  , text :: String
  , synthetic :: Boolean
  }

-- | Tool part data
type ToolPartData =
  { id :: String
  , callID :: String
  , tool :: String
  , state :: ToolState
  }

-- | Tool execution state
type ToolState =
  { status :: String  -- "pending" | "running" | "completed" | "error"
  , input :: Object String
  , output :: Maybe String
  , error :: Maybe String
  , metadata :: Object String
  }

-- | Reasoning part data
type ReasoningPartData =
  { id :: String
  , text :: String
  }

-- | File part data
type FilePartData =
  { id :: String
  , mime :: String
  , filename :: Maybe String
  , url :: Maybe String
  , source :: Maybe { text :: Maybe { start :: Int, end :: Int } }
  }

-- | Agent part data
type AgentPartData =
  { id :: String
  , source :: Maybe { start :: Int, end :: Int }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- DIAGNOSTIC & TODO TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Diagnostic type (LSP-style)
type Diagnostic =
  { range ::
      { start :: { line :: Int, character :: Int }
      , end :: { line :: Int, character :: Int }
      }
  , message :: String
  , severity :: Maybe Int  -- 1 = Error, 2 = Warning, etc.
  }

-- | Todo item
type Todo =
  { id :: String
  , content :: String
  , status :: String  -- "pending" | "in_progress" | "completed" | "cancelled"
  , priority :: String  -- "high" | "medium" | "low"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUESTION TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Question option
type QuestionOption =
  { label :: String
  , description :: Maybe String
  }

-- | Question info
type QuestionInfo =
  { question :: String
  , header :: String
  , options :: Array QuestionOption
  , multiple :: Boolean
  }

-- | Question answer (array of selected labels)
type QuestionAnswer = Array String

-- ═══════════════════════════════════════════════════════════════════════════════
-- TOOL & COMPONENT TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tool display info
type ToolInfo =
  { icon :: String
  , title :: String
  , subtitle :: Maybe String
  }

-- | Message component props
type MessageProps =
  { message :: Message
  , parts :: Array Part
  }

-- | Message part component props
type MessagePartProps =
  { part :: Part
  , message :: Message
  , hideDetails :: Boolean
  , defaultOpen :: Boolean
  }

-- | Tool component props
type ToolProps =
  { input :: Object String
  , metadata :: Object String
  , tool :: String
  , output :: Maybe String
  , status :: Maybe String
  , hideDetails :: Boolean
  , defaultOpen :: Boolean
  , forceOpen :: Boolean
  , locked :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- PERMISSION TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Permission request
type PermissionRequest =
  { id :: String
  , sessionID :: String
  , tool :: Maybe { callID :: String, messageID :: String }
  , metadata :: Object String
  }

-- | Permission response options
data PermissionResponse
  = AllowOnce
  | AllowAlways
  | Reject

derive instance eqPermissionResponse :: Eq PermissionResponse
