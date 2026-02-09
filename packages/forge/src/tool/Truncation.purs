-- | Output truncation utilities
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/truncation.ts
module Forge.Tool.Truncation
  ( maxLines
  , maxBytesLimit
  , TruncateResult
  , TruncateOptions
  , init
  , cleanup
  , output
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Maximum lines before truncation
foreign import maxLines :: Int

-- | Maximum bytes before truncation
foreign import maxBytesLimit :: Int

-- | Truncation result
type TruncateResult =
  { content :: String
  , truncated :: Boolean
  , outputPath :: Maybe String
  }

-- | Truncation options
type TruncateOptions =
  { maxLines :: Maybe Int
  , maxBytes :: Maybe Int
  , direction :: Maybe String  -- "head" | "tail"
  }

-- | Initialize truncation cleanup scheduler
foreign import init :: Effect Unit

-- | Clean up old truncation files
foreign import cleanup :: Aff Unit

-- | Truncate output if needed, saving full output to file
foreign import output :: String -> TruncateOptions -> Foreign -> Aff TruncateResult
