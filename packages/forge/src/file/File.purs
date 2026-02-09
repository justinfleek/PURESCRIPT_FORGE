-- | File operations
-- | 1:1 parity with opencode-dev/packages/opencode/src/file/file.ts
module Forge.File.File where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | File info type
type FileInfo =
  { path :: String
  , name :: String
  , size :: Int
  , isDirectory :: Boolean
  , modifiedAt :: Number
  }

-- | Read file contents
foreign import read :: String -> Aff (Either String String)

-- | Write file contents
foreign import write :: String -> String -> Aff (Either String Unit)

-- | Check if file exists
foreign import exists :: String -> Aff Boolean

-- | Get file info
foreign import info :: String -> Aff (Either String FileInfo)

-- | Delete file
foreign import remove :: String -> Aff (Either String Unit)

-- | Create directory
foreign import mkdir :: String -> Aff (Either String Unit)

-- | List directory contents
foreign import readdir :: String -> Aff (Either String (Array String))
