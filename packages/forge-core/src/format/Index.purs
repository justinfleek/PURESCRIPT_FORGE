-- | Format Index
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/format/index.ts
module Forge.Format.Index where

import Forge.Format.Formatter as Formatter

-- Re-export formatter functions
format :: String -> Formatter.FormatConfig -> _
format = Formatter.format

formatFile :: String -> _
formatFile = Formatter.formatFile
