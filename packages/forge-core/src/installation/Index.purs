-- | Installation management
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/installation/index.ts
module Forge.Installation.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

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
