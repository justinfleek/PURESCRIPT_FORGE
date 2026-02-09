-- | Multi-edit tool (sequential edits on single file)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/multiedit.ts
module Forge.Tool.Multiedit
  ( MultieditParams
  , EditOperation
  , ToolContext
  , ToolResult
  , execute
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Single edit operation
type EditOperation =
  { filePath :: String
  , oldString :: String
  , newString :: String
  , replaceAll :: Maybe Boolean
  }

-- | Multiedit parameters
type MultieditParams =
  { filePath :: String
  , edits :: Array EditOperation
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
  }

-- | Execute multi-edit (sequential edits on file)
foreign import execute :: MultieditParams -> ToolContext -> Aff ToolResult
