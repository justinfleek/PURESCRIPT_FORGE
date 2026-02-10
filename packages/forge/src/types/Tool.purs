-- | PureScript type definitions for OpenCode Tool types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/tool/
module Opencode.Types.Tool where

import Prelude

import Data.Argonaut (Json)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)
import Foreign.Object (Object)

-- | Tool identifier
type ToolID = String

-- | Session identifier
type SessionID = String

-- | Message identifier
type MessageID = String

-- | Agent identifier
type AgentID = String

-- | Tool metadata - sum type for all possible tool metadata
-- | Each tool defines its own metadata type
data ToolMetadata
  = SearchMetadata { query :: String, categories :: Array String, limit :: Int, resultsCount :: Int, searchTimeMs :: Int }
  | TodoMetadata { todos :: Array { id :: String, content :: String, status :: String, priority :: String } }
  | BatchMetadata { totalCalls :: Int, successful :: Int, failed :: Int, tools :: Array String }
  | MultieditMetadata { filePath :: String, relativePath :: String, editsApplied :: Int }
  | QuestionMetadata { questions :: Array { question :: String, header :: String, options :: Array { label :: String, description :: String } }, answered :: Boolean }
  | LsMetadata { count :: Int, totalFiles :: Int, totalDirs :: Int, truncated :: Boolean }
  | SkillMetadata { name :: String, dir :: String }
  | LspMetadata { operation :: String, filePath :: String, position :: { line :: Int, character :: Int }, results :: Array { resultType :: String, text :: String } }
  | CodesearchMetadata { query :: String, tokensNum :: Int, resultsCount :: Int }
  | TaskMetadata { sessionId :: String, agentType :: String, status :: String }
  | PlanMetadata { agent :: String, plan :: String }
  | ErrorMetadata { error :: String }
  | EmptyMetadata

derive instance eqToolMetadata :: Eq ToolMetadata
derive instance genericToolMetadata :: Generic ToolMetadata _

instance showToolMetadata :: Show ToolMetadata where
  show = genericShow

-- | Tool initialization context
type ToolInitContext =
  { agent :: Maybe AgentInfo
  }

-- | Agent information
type AgentInfo = { id :: String, name :: String }

-- | Tool execution context
type ToolContext =
  { sessionID :: SessionID
  , messageID :: MessageID
  , agent :: AgentID
  , abort :: AbortSignal
  , callID :: Maybe String
  , extra :: Maybe (Object Json)
  , messages :: Array MessageWithParts
  }

-- | Abort signal
data AbortSignal = AbortSignal

derive instance genericAbortSignal :: Generic AbortSignal _
derive instance eqAbortSignal :: Eq AbortSignal

instance showAbortSignal :: Show AbortSignal where
  show = genericShow

-- | Message part type (tool-local)
data MessagePartType = TextPart | CodePart | DiffPart | BashPart | ErrorPart | MarkdownPart

derive instance eqMessagePartType :: Eq MessagePartType
derive instance genericMessagePartType :: Generic MessagePartType _

instance showMessagePartType :: Show MessagePartType where
  show = genericShow

-- | Message part (typed instead of Json)
type MessagePart =
  { partType :: MessagePartType
  , content :: String
  , language :: Maybe String
  , path :: Maybe String
  }

-- | Message with parts
type MessageWithParts = { id :: String, parts :: Array MessagePart }

-- | Tool execution result
type ToolResult =
  { title :: String
  , metadata :: ToolMetadata
  , output :: String
  , attachments :: Maybe (Array FilePart)
  }

-- | File part
type FilePart = { path :: String, content :: String }

-- | Tool information
-- | Note: This is simplified - the actual TypeScript version uses generics
-- | PureScript would need higher-kinded types or a different approach
type ToolInfo =
  { id :: ToolID
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

-- | Tool truncation result
data TruncationResult
  = NotTruncated { content :: String }
  | Truncated { content :: String, outputPath :: String }

derive instance genericTruncationResult :: Generic TruncationResult _
derive instance eqTruncationResult :: Eq TruncationResult

instance showTruncationResult :: Show TruncationResult where
  show = genericShow
