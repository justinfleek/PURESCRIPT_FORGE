-- | Installation management
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/installation/index.ts
module Opencode.Installation.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Installation info
type InstallationInfo =
  { version :: String
  , path :: String
  , installedAt :: Number
  }

-- | Get installation info
getInfo :: Aff (Either String InstallationInfo)
getInfo = notImplemented "Installation.Index.getInfo"

-- | Check for updates
checkUpdates :: Aff (Either String (Maybe String))
checkUpdates = notImplemented "Installation.Index.checkUpdates"
