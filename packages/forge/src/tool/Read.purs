-- | File reading tool
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/read.ts
module Forge.Tool.Read
  ( ReadParams
  , execute
  , defaultReadLimit
  , maxLineLength
  , maxBytes
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Constants
foreign import defaultReadLimit :: Int
foreign import maxLineLength :: Int
foreign import maxBytes :: Int

-- | Read parameters
type ReadParams =
  { filePath :: String
  , offset :: Maybe Int
  , limit :: Maybe Int
  }

-- | Tool context
type ToolContext =
  { sessionID :: String
  , messageID :: String
  , callID :: String
  , abort :: Foreign
  , ask :: Foreign -> Aff Unit
  , metadata :: Foreign -> Aff Unit
  , messages :: Foreign
  , extra :: Foreign
  }

-- | Tool result
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Foreign
  , attachments :: Foreign
  }

-- | Execute read tool
foreign import execute :: ReadParams -> ToolContext -> Aff ToolResult
