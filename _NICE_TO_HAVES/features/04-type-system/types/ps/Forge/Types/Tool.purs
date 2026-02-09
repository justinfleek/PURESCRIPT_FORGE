-- | PureScript type definitions for Forge Tool types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from forge-dev/packages/forge/src/tool/
module Forge.Types.Tool where

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

-- | Tool metadata (simplified - would be extensible)
type ToolMetadata = Record String Json

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

-- | Message with parts (placeholder - would import from Message module)
type MessageWithParts = { id :: String, parts :: Array Json }

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
