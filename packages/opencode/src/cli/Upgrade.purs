-- | CLI Upgrade functionality
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/upgrade.ts
module Opencode.CLI.Upgrade where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Version information
type VersionInfo =
  { current :: String
  , latest :: String
  , updateAvailable :: Boolean
  }

-- | Check for available updates
checkForUpdates :: Aff (Either String VersionInfo)
checkForUpdates = notImplemented "CLI.Upgrade.checkForUpdates"

-- | Perform the upgrade
performUpgrade :: String -> Aff (Either String Unit)
performUpgrade version = notImplemented "CLI.Upgrade.performUpgrade"

-- | Get current version
getCurrentVersion :: String
getCurrentVersion = "0.1.0" -- TODO: Read from package.json equivalent
