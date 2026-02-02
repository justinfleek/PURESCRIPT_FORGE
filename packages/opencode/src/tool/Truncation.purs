-- | Truncation.purs - Output truncation
-- | TODO: Implement - mirrors opencode/src/tool/truncation.ts
module Tool.Truncation where

import Prelude
import Effect.Aff (Aff)

maxLines :: Int
maxLines = 2000

maxBytes :: Int
maxBytes = 51200

type TruncateResult = { content :: String, truncated :: Boolean, outputPath :: String }

truncateOutput :: String -> Aff TruncateResult
truncateOutput _ = notImplemented "Tool.Truncation.truncateOutput"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
