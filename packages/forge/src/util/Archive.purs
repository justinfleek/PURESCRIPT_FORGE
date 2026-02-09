-- | Archive utilities (zip extraction)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/archive.ts
module Forge.Util.Archive
  ( extractZip
  ) where

import Prelude
import Effect.Aff (Aff)

-- | Extract a zip archive to destination directory
-- | Uses PowerShell on Windows, unzip on Unix
foreign import extractZip :: String -> String -> Aff Unit
