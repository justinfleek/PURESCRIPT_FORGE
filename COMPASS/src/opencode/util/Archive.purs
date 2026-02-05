-- | Archive utilities
module Opencode.Util.Archive where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

-- | Create a zip archive
createZip :: String -> Array String -> Aff (Either String String)
createZip outputPath files = createZipArchive outputPath files

-- | Extract a zip archive
extractZip :: String -> String -> Aff (Either String Unit)
extractZip archivePath outputDir = extractZipArchive archivePath outputDir

foreign import createZipArchive :: String -> Array String -> Aff (Either String String)
foreign import extractZipArchive :: String -> String -> Aff (Either String Unit)
