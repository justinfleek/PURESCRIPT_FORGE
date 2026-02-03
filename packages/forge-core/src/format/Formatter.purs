-- | Code Formatter
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/format/formatter.ts
module Forge.Format.Formatter where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

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
