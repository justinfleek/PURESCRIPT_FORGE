-- | Apply unified diff patches tool
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/apply_patch.ts
module Forge.Tool.ApplyPatch
  ( ApplyPatchParams
  , FileChange
  , ToolContext
  , ToolResult
  , execute
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Apply patch parameters
type ApplyPatchParams =
  { patchText :: String
  }

-- | Individual file change info
type FileChange =
  { filePath :: String
  , relativePath :: String
  , type :: String  -- "add" | "update" | "delete" | "move"
  , diff :: String
  , before :: String
  , after :: String
  , additions :: Int
  , deletions :: Int
  , movePath :: Maybe String
  }

-- | Tool context
type ToolContext =
  { sessionID :: String
  , messageID :: String
  , callID :: String
  , ask :: Foreign -> Aff Unit
  }

-- | Tool result
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Foreign
  }

-- | Execute apply_patch
foreign import execute :: ApplyPatchParams -> ToolContext -> Aff ToolResult
