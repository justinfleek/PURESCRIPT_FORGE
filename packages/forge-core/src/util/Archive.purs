-- | Archive utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/archive.ts
module Forge.Util.Archive where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Create a zip archive
createZip :: String -> Array String -> Aff (Either String String)
createZip outputPath files = notImplemented "Util.Archive.createZip"

-- | Extract a zip archive
extractZip :: String -> String -> Aff (Either String Unit)
extractZip archivePath outputDir = notImplemented "Util.Archive.extractZip"
