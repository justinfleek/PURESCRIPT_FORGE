-- | File editing tool (exact string replacement)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/edit.ts
module Forge.Tool.Edit
  ( EditParams
  , ToolContext
  , ToolResult
  , execute
  , trimDiff
  , replace
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Edit parameters
type EditParams =
  { filePath :: String
  , oldString :: String
  , newString :: String
  , replaceAll :: Maybe Boolean
  }

-- | Tool context
type ToolContext =
  { sessionID :: String
  , messageID :: String
  , callID :: String
  , ask :: Foreign -> Aff Unit
  , metadata :: Foreign -> Aff Unit
  }

-- | Tool result
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Foreign
  }

-- | Execute edit tool
foreign import execute :: EditParams -> ToolContext -> Aff ToolResult

-- | Trim common indentation from diff output
foreign import trimDiff :: String -> String

-- | Replace oldString with newString in content
-- | Uses multiple replacement strategies (simple, trimmed, block anchor, etc.)
foreign import replace :: String -> String -> String -> Boolean -> String
