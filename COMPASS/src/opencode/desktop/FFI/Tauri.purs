-- | Desktop Tauri FFI - Tauri API bindings
-- | Phase 5: Desktop/Web Migration
module Opencode.Desktop.FFI.Tauri where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Array (Array)

-- | Menu item type
foreign import data MenuItem :: Type

-- | Update type
type Update =
  { version :: String
  }

-- | Message options
type MessageOptions =
  { title :: String
  }

-- | Invoke Tauri command to install CLI
foreign import invokeInstallCLI :: Effect (Either String String)

-- | Show message dialog
foreign import showMessage :: String -> MessageOptions -> Effect Unit

-- | Show ask dialog
foreign import ask :: String -> MessageOptions -> Aff Boolean

-- | Get OS type
foreign import getOSType :: Effect String

-- | Create menu
foreign import createMenu :: Array MenuItem -> Effect Unit

-- | Set as app menu
foreign import setAsAppMenu :: Effect Unit

-- | Create submenu
foreign import createSubmenu :: String -> Array MenuItem -> Aff MenuItem

-- | Create menu item
foreign import menuItem :: String -> Aff Unit -> MenuItem

-- | Create predefined menu item
foreign import predefinedMenuItem :: String -> MenuItem

-- | Check for updates
foreign import checkForUpdates :: Effect (Either String (Maybe Update))

-- | Download update
foreign import downloadUpdate :: Update -> Aff (Either String Unit)

-- | Install update
foreign import installUpdate :: Update -> Aff (Either String Unit)

-- | Reload webview
foreign import reloadWebview :: Effect Unit

-- | Relaunch application
foreign import relaunch :: Effect Unit

-- | Kill sidecar process
foreign import killSidecar :: Effect Unit

-- | Set webview zoom level
foreign import setWebviewZoom :: Number -> Effect Unit

-- | Get webview zoom level
foreign import getWebviewZoom :: Effect Number
