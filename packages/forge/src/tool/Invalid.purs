-- | Invalid tool (placeholder for malformed tool calls)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/invalid.ts
module Forge.Tool.Invalid
  ( InvalidParams
  , ToolResult
  , execute
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | Invalid tool parameters
type InvalidParams =
  { tool :: String
  , error :: String
  }

-- | Result type
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Foreign
  }

-- | Execute invalid tool (returns error message)
foreign import execute :: InvalidParams -> Aff ToolResult
