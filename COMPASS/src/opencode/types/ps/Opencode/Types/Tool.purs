-- | PureScript type definitions for OpenCode Tool types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/tool/
module Opencode.Types.Tool where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))

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
  | LspMetadata { operation :: String, filePath :: String, position :: { line :: Int, character :: Int }, results :: Array { type :: String, text :: String } }
  | CodesearchMetadata { query :: String, tokensNum :: Int, resultsCount :: Int }
  | TaskMetadata { sessionId :: String, agentType :: String, status :: String }
  | PlanMetadata { agent :: String, plan :: String }
  | ErrorMetadata { error :: String }
  | EmptyMetadata

derive instance eqToolMetadata :: Eq ToolMetadata
derive instance genericToolMetadata :: Generic ToolMetadata _

-- | Tool initialization context
type ToolInitContext =
  { agent :: Maybe AgentInfo
  }

-- | Agent information (placeholder - would import from Agent module)
type AgentInfo = { id :: String, name :: String }

-- | Tool execution context
type ToolContext =
  { sessionID :: SessionID
  , messageID :: MessageID
  , agent :: AgentID
  , abort :: AbortSignal  -- Placeholder - would be Effect-based
  , callID :: Maybe String
  , extra :: Maybe (Record String Json)
  , messages :: Array MessageWithParts  -- Placeholder - would import from Message module
  }

-- | Abort signal (placeholder - would be Effect-based)
data AbortSignal = AbortSignal

derive instance genericAbortSignal :: Generic AbortSignal _
derive instance eqAbortSignal :: Eq AbortSignal

instance showAbortSignal :: Show AbortSignal where
  show = genericShow

-- | Message part type
data MessagePartType = TextPart | CodePart | DiffPart | BashPart | ErrorPart | MarkdownPart

derive instance eqMessagePartType :: Eq MessagePartType
derive instance genericMessagePartType :: Generic MessagePartType _

-- | Message part (typed instead of Json)
type MessagePart =
  { type :: MessagePartType
  , content :: String
  , language :: Maybe String
  , path :: Maybe String
  }

-- | Message with parts (placeholder - would import from Message module)
type MessageWithParts = { id :: String, parts :: Array MessagePart }

-- | Tool execution result
type ToolResult =
  { title :: String
  , metadata :: ToolMetadata
  , output :: String
  , attachments :: Maybe (Array FilePart)
  }

-- | File part (placeholder - would import from Message module)
type FilePart = { path :: String, content :: String }

-- | Tool information
-- | Note: This is simplified - the actual TypeScript version uses generics
-- | PureScript would need higher-kinded types or a different approach
type ToolInfo =
  { id :: ToolID
  , description :: String
  , parameters :: Json  -- Zod schema encoded as JSON
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

derive instance genericToolInfo :: Generic ToolInfo _
derive instance eqToolInfo :: Eq ToolInfo

instance showToolInfo :: Show ToolInfo where
  show = genericShow

-- | Tool truncation result
data TruncationResult
  = NotTruncated { content :: String }
  | Truncated { content :: String, outputPath :: String }

derive instance genericTruncationResult :: Generic TruncationResult _
derive instance eqTruncationResult :: Eq TruncationResult

instance showTruncationResult :: Show TruncationResult where
  show = genericShow

-- Import Effect for ToolResult
import Effect (Effect)
import Effect.Aff (Aff)
