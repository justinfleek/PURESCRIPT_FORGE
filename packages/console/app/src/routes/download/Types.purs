-- | Download Platform Types
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/download/types.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Download.Types
  ( DownloadPlatform(..)
  , allPlatforms
  , platformToString
  , parsePlatform
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Download platform variants
data DownloadPlatform
  = DarwinAarch64Dmg
  | DarwinX64Dmg
  | WindowsX64Nsis
  | LinuxX64Deb
  | LinuxX64Rpm
  | LinuxX64AppImage

derive instance eqDownloadPlatform :: Eq DownloadPlatform
derive instance ordDownloadPlatform :: Ord DownloadPlatform

instance showDownloadPlatform :: Show DownloadPlatform where
  show DarwinAarch64Dmg = "darwin-aarch64-dmg"
  show DarwinX64Dmg = "darwin-x64-dmg"
  show WindowsX64Nsis = "windows-x64-nsis"
  show LinuxX64Deb = "linux-x64-deb"
  show LinuxX64Rpm = "linux-x64-rpm"
  show LinuxX64AppImage = "linux-x64-appimage"

-- | All available platforms
allPlatforms :: Array DownloadPlatform
allPlatforms =
  [ DarwinAarch64Dmg
  , DarwinX64Dmg
  , WindowsX64Nsis
  , LinuxX64Deb
  , LinuxX64Rpm
  , LinuxX64AppImage
  ]

-- | Convert platform to string
platformToString :: DownloadPlatform -> String
platformToString = show

-- | Parse platform from string
parsePlatform :: String -> Maybe DownloadPlatform
parsePlatform "darwin-aarch64-dmg" = Just DarwinAarch64Dmg
parsePlatform "darwin-x64-dmg" = Just DarwinX64Dmg
parsePlatform "windows-x64-nsis" = Just WindowsX64Nsis
parsePlatform "linux-x64-deb" = Just LinuxX64Deb
parsePlatform "linux-x64-rpm" = Just LinuxX64Rpm
parsePlatform "linux-x64-appimage" = Just LinuxX64AppImage
parsePlatform _ = Nothing
