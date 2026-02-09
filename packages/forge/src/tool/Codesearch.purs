-- | Code search tool (external API for code context)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/codesearch.ts
module Forge.Tool.Codesearch
  ( CodesearchParams
  , ToolContext
  , ToolResult
  , execute
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Codesearch parameters
type CodesearchParams =
  { query :: String
  , tokensNum :: Maybe Int  -- 1000-50000, default 5000
  }

-- | Tool context
type ToolContext =
  { sessionID :: String
  , messageID :: String
  , callID :: String
  , abort :: Foreign  -- AbortSignal
  , ask :: Foreign -> Aff Unit
  , metadata :: Foreign -> Aff Unit
  }

-- | Tool result
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Foreign
  }

-- | Execute codesearch
foreign import execute :: CodesearchParams -> ToolContext -> Aff ToolResult
