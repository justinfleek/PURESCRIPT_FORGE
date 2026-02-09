-- | Bash command execution tool
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/bash.ts
module Forge.Tool.Bash
  ( BashParams
  , execute
  , defaultTimeout
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Default timeout in ms (2 minutes)
foreign import defaultTimeout :: Int

-- | Bash parameters
type BashParams =
  { command :: String
  , timeout :: Maybe Int
  , workdir :: Maybe String
  , description :: String
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

-- | Execute bash command
foreign import execute :: BashParams -> ToolContext -> Aff ToolResult
