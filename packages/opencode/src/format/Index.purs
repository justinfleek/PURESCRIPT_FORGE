-- | Format Index
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/format/index.ts
module Opencode.Format.Index where

import Opencode.Format.Formatter as Formatter

-- Re-export formatter functions
format :: String -> Formatter.FormatConfig -> _
format = Formatter.format

formatFile :: String -> _
formatFile = Formatter.formatFile
