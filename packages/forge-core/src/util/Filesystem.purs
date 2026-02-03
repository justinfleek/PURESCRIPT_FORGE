-- | Filesystem utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/filesystem.ts
module Forge.Util.Filesystem where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Check if path exists
exists :: String -> Aff Boolean
exists path = notImplemented "Util.Filesystem.exists"

-- | Check if path is a directory
isDirectory :: String -> Aff Boolean
isDirectory path = notImplemented "Util.Filesystem.isDirectory"

-- | Check if path is a file
isFile :: String -> Aff Boolean
isFile path = notImplemented "Util.Filesystem.isFile"

-- | Get file size
getSize :: String -> Aff (Either String Int)
getSize path = notImplemented "Util.Filesystem.getSize"

-- | Read directory contents
readDir :: String -> Aff (Either String (Array String))
readDir path = notImplemented "Util.Filesystem.readDir"

-- | Create directory recursively
mkdirp :: String -> Aff (Either String Unit)
mkdirp path = notImplemented "Util.Filesystem.mkdirp"
