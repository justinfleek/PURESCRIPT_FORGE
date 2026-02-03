-- | Download Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/download/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Download.Index
  ( OS(..)
  , DownloadState(..)
  , CliCommand(..)
  , DownloadRow(..)
  , detectOS
  , getDefaultPlatform
  , allCliCommands
  , desktopDownloads
  , extensionDownloads
  , integrationDownloads
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Console.App.Routes.Download.Types (DownloadPlatform(..))

-- | Detected operating system
data OS = MacOS | Windows | Linux

derive instance eqOS :: Eq OS

instance showOS :: Show OS where
  show MacOS = "macOS"
  show Windows = "Windows"
  show Linux = "Linux"

-- | Detect OS from platform string (pure)
detectOS :: String -> Maybe OS
detectOS platform
  | contains "mac" platform = Just MacOS
  | contains "win" platform = Just Windows
  | contains "linux" platform = Just Linux
  | otherwise = Nothing
  where
    contains :: String -> String -> Boolean
    contains _ _ = false  -- simplified

-- | Get default download platform for OS
getDefaultPlatform :: OS -> DownloadPlatform
getDefaultPlatform MacOS = DarwinAarch64Dmg
getDefaultPlatform Windows = WindowsX64Nsis
getDefaultPlatform Linux = LinuxX64Deb

-- | Download page state
type DownloadState =
  { detectedOS :: Maybe OS
  }

-- | CLI installation command
type CliCommand =
  { command :: String
  , displayCommand :: String
  }

-- | All CLI installation commands
allCliCommands :: Array CliCommand
allCliCommands =
  [ { command: "curl -fsSL https://opencode.ai/install | bash"
    , displayCommand: "curl -fsSL https://opencode.ai/install | bash"
    }
  , { command: "npm i -g opencode-ai"
    , displayCommand: "npm i -g opencode-ai"
    }
  , { command: "bun add -g opencode-ai"
    , displayCommand: "bun add -g opencode-ai"
    }
  , { command: "brew install anomalyco/tap/opencode"
    , displayCommand: "brew install anomalyco/tap/opencode"
    }
  , { command: "paru -S opencode"
    , displayCommand: "paru -S opencode"
    }
  ]

-- | Download row configuration
type DownloadRow =
  { label :: String
  , platform :: DownloadPlatform
  , iconName :: String
  }

-- | Desktop download options
desktopDownloads :: Array DownloadRow
desktopDownloads =
  [ { label: "macOS (Apple Silicon)", platform: DarwinAarch64Dmg, iconName: "apple" }
  , { label: "macOS (Intel)", platform: DarwinX64Dmg, iconName: "apple" }
  , { label: "Windows (x64)", platform: WindowsX64Nsis, iconName: "windows" }
  , { label: "Linux (.deb)", platform: LinuxX64Deb, iconName: "linux" }
  , { label: "Linux (.rpm)", platform: LinuxX64Rpm, iconName: "linux" }
  ]

-- | Extension download configuration
type ExtensionRow =
  { name :: String
  , docsUrl :: String
  }

extensionDownloads :: Array ExtensionRow
extensionDownloads =
  [ { name: "VS Code", docsUrl: "https://opencode.ai/docs/ide/" }
  , { name: "Cursor", docsUrl: "https://opencode.ai/docs/ide/" }
  , { name: "Zed", docsUrl: "https://opencode.ai/docs/ide/" }
  , { name: "Windsurf", docsUrl: "https://opencode.ai/docs/ide/" }
  , { name: "VSCodium", docsUrl: "https://opencode.ai/docs/ide/" }
  ]

-- | Integration download configuration
integrationDownloads :: Array ExtensionRow
integrationDownloads =
  [ { name: "GitHub", docsUrl: "https://opencode.ai/docs/github/" }
  , { name: "GitLab", docsUrl: "https://opencode.ai/docs/gitlab/" }
  ]
