-- | CLI Upgrade functionality
module Opencode.CLI.Upgrade where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String

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
getCurrentVersion = unsafePerformEffect $ do
  version <- readPackageVersion
  pure $ fromMaybe "0.1.0" version
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a
    foreign import readPackageVersion :: Effect (Maybe String)
