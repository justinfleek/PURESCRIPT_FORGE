-- | File Index
-- | 1:1 parity with opencode-dev/packages/opencode/src/file/index.ts
module Forge.File.Index
  ( module Forge.File.File
  ) where

import Forge.File.File (FileInfo, read, write, exists, info, remove, mkdir, readdir)
