-- | Batch tool execution (parallel tool calls)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/batch.ts
module Forge.Tool.Batch
  ( BatchParams
  , ToolCall
  , ToolContext
  , ToolResult
  , execute
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | Single tool call
type ToolCall =
  { tool :: String
  , parameters :: Foreign
  }

-- | Batch parameters
type BatchParams =
  { tool_calls :: Array ToolCall
  }

-- | Tool context
type ToolContext =
  { sessionID :: String
  , messageID :: String
  , callID :: String
  }

-- | Tool result
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Foreign
  , attachments :: Foreign
  }

-- | Execute batch (parallel tool execution)
foreign import execute :: BatchParams -> ToolContext -> Aff ToolResult
