-- | File time utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/file/time.ts
module Forge.File.Time where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | File time info
type FileTime =
  { created :: Number
  , modified :: Number
  , accessed :: Number
  }

-- | Get file times
getFileTimes :: String -> Aff (Either String FileTime)
getFileTimes path = notImplemented "File.Time.getFileTimes"

-- | Touch a file (update modified time)
touch :: String -> Aff (Either String Unit)
touch path = notImplemented "File.Time.touch"
