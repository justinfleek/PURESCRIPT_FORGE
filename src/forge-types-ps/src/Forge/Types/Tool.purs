-- | PureScript type definitions for Forge Tool types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from forge-dev/packages/forge/src/tool/
module Forge.Types.Tool where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (Json)
import Effect.Aff (Aff)

-- | Tool identifier
type ToolID = String

-- | Session identifier
type SessionID = String

-- | Message identifier
type MessageID = String

-- | Agent identifier
type AgentID = String

-- | Tool metadata (simplified)
type ToolMetadata = { extra :: Maybe Json }

-- | Agent information
type AgentInfo = { id :: String, name :: String }

-- | Tool initialization context
type ToolInitContext =
  { agent :: Maybe AgentInfo
  }

-- | Message with parts (placeholder)
type MessageWithParts = { id :: String, parts :: Array Json }

-- | Abort signal (placeholder)
data AbortSignal = AbortSignal

derive instance genericAbortSignal :: Generic AbortSignal _
derive instance eqAbortSignal :: Eq AbortSignal

instance showAbortSignal :: Show AbortSignal where
  show = genericShow

-- | Tool execution context
type ToolContext =
  { sessionID :: SessionID
  , messageID :: MessageID
  , agent :: AgentID
  , callID :: Maybe String
  , extra :: Maybe Json
  , messages :: Array MessageWithParts
  }

-- | File part
type FilePart = { path :: String, content :: String }

-- | Tool execution result
type ToolResult =
  { title :: String
  , metadata :: ToolMetadata
  , output :: String
  , attachments :: Maybe (Array FilePart)
  }

-- | Tool information (simplified - no functions in type)
type ToolInfo =
  { id :: ToolID
  , description :: String
  , parameters :: Json
  }

-- | Tool truncation result
data TruncationResult
  = NotTruncated String
  | Truncated { content :: String, outputPath :: String }

derive instance genericTruncationResult :: Generic TruncationResult _
derive instance eqTruncationResult :: Eq TruncationResult

instance showTruncationResult :: Show TruncationResult where
  show = genericShow
