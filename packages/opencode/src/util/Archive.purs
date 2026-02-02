-- | Archive utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/archive.ts
module Opencode.Util.Archive where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Create a zip archive
createZip :: String -> Array String -> Aff (Either String String)
createZip outputPath files = notImplemented "Util.Archive.createZip"

-- | Extract a zip archive
extractZip :: String -> String -> Aff (Either String Unit)
extractZip archivePath outputDir = notImplemented "Util.Archive.extractZip"
