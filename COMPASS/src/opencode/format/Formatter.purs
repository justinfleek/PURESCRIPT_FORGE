-- | Code Formatter
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/format/formatter.ts
module Opencode.Format.Formatter where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Format configuration
type FormatConfig =
  { language :: Maybe String
  , indentSize :: Int
  , useTabs :: Boolean
  }

-- | Format code
format :: String -> FormatConfig -> Aff (Either String String)
format code config = notImplemented "Format.Formatter.format"

-- | Format a file
formatFile :: String -> Aff (Either String Unit)
formatFile path = notImplemented "Format.Formatter.formatFile"
