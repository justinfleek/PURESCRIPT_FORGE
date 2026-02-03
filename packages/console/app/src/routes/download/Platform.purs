-- | Download Platform Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/download/[platform].ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Download.Platform
  ( AssetMapping(..)
  , DownloadMapping(..)
  , getAssetName
  , getDownloadName
  , buildDownloadUrl
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Console.App.Routes.Download.Types (DownloadPlatform(..))

-- | Asset file name mapping
type AssetMapping = Map DownloadPlatform String

-- | Asset names on GitHub releases
assetNames :: AssetMapping
assetNames = Map.fromFoldable
  [ Tuple DarwinAarch64Dmg "opencode-desktop-darwin-aarch64.dmg"
  , Tuple DarwinX64Dmg "opencode-desktop-darwin-x64.dmg"
  , Tuple WindowsX64Nsis "opencode-desktop-windows-x64.exe"
  , Tuple LinuxX64Deb "opencode-desktop-linux-amd64.deb"
  , Tuple LinuxX64AppImage "opencode-desktop-linux-amd64.AppImage"
  , Tuple LinuxX64Rpm "opencode-desktop-linux-x86_64.rpm"
  ]
  where
    Tuple a b = { key: a, value: b }

-- | Download file name mapping (user-friendly names)
type DownloadMapping = Map DownloadPlatform String

downloadNames :: DownloadMapping
downloadNames = Map.fromFoldable
  [ Tuple DarwinAarch64Dmg "OpenCode Desktop.dmg"
  , Tuple DarwinX64Dmg "OpenCode Desktop.dmg"
  , Tuple WindowsX64Nsis "OpenCode Desktop Installer.exe"
  ]
  where
    Tuple a b = { key: a, value: b }

-- | Get asset name for platform
getAssetName :: DownloadPlatform -> Maybe String
getAssetName platform = Map.lookup platform assetNames

-- | Get user-friendly download name
getDownloadName :: DownloadPlatform -> Maybe String
getDownloadName platform = Map.lookup platform downloadNames

-- | Build GitHub download URL
buildDownloadUrl :: String -> String
buildDownloadUrl assetName =
  "https://github.com/anomalyco/opencode/releases/latest/download/" <> assetName
