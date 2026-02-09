-- | Tool module - 1:1 parity with opencode-dev/src/tool/tool.ts
module Forge.Tool.Tool
  ( -- * Types
    ToolInfo
  , ToolContext
  , ToolResult
  , ToolMetadata
  , InitContext
    -- * Functions
  , define
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Tool metadata (arbitrary key-value pairs)
type ToolMetadata = Foreign

-- | Tool initialization context
type InitContext =
  { agent :: Maybe Foreign  -- Agent.Info
  }

-- | Tool execution context
type ToolContext =
  { sessionID :: String
  , messageID :: String
  , agent :: String
  , abort :: Foreign        -- AbortSignal
  , callID :: Maybe String
  , extra :: Maybe Foreign
  , messages :: Array Foreign  -- MessageV2.WithParts[]
  }

-- | Tool execution result
type ToolResult =
  { title :: String
  , metadata :: ToolMetadata
  , output :: String
  , attachments :: Maybe (Array Foreign)  -- MessageV2.FilePart[]
  }

-- | Tool information/definition
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Foreign    -- Zod schema
  , execute :: Foreign -> ToolContext -> Aff ToolResult
  }

-- | Define a new tool
foreign import defineFFI :: String -> (Maybe InitContext -> Aff ToolInfo) -> ToolInfo

define :: String -> (Maybe InitContext -> Aff ToolInfo) -> ToolInfo
define = defineFFI
