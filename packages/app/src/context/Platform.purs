-- | Platform context - provides platform-specific capabilities
-- | Migrated from: forge-dev/packages/app/src/context/platform.tsx
module Sidepanel.Context.Platform
  ( Platform
  , PlatformType(..)
  , OperatingSystem(..)
  , DirectoryPickerOptions
  , FilePickerOptions
  , SaveFilePickerOptions
  , UpdateCheckResult
  , mkPlatform
  , openLink
  , restart
  , back
  , forward
  , notify
  , openDirectoryPickerDialog
  , openFilePickerDialog
  , saveFilePickerDialog
  , checkUpdate
  , update
  , getDefaultServerUrl
  , setDefaultServerUrl
  , parseMarkdown
  , platformType
  , os
  , version
  , customFetch
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)

-- | Platform discriminator
data PlatformType
  = Web
  | Desktop

derive instance eqPlatformType :: Eq PlatformType

instance showPlatformType :: Show PlatformType where
  show Web = "web"
  show Desktop = "desktop"

-- | Desktop operating system (Tauri only)
data OperatingSystem
  = MacOS
  | Windows
  | Linux

derive instance eqOperatingSystem :: Eq OperatingSystem

instance showOperatingSystem :: Show OperatingSystem where
  show MacOS = "macos"
  show Windows = "windows"
  show Linux = "linux"

-- | Directory picker options
type DirectoryPickerOptions =
  { title :: Maybe String
  , multiple :: Maybe Boolean
  }

-- | File picker options
type FilePickerOptions =
  { title :: Maybe String
  , multiple :: Maybe Boolean
  }

-- | Save file picker options
type SaveFilePickerOptions =
  { title :: Maybe String
  , defaultPath :: Maybe String
  }

-- | Update check result
type UpdateCheckResult =
  { updateAvailable :: Boolean
  , version :: Maybe String
  }

-- | Platform capabilities record
type Platform =
  { platformType :: PlatformType
  , os :: Maybe OperatingSystem
  , version :: Maybe String
  , openLink :: String -> Effect Unit
  , restart :: Aff Unit
  , back :: Effect Unit
  , forward :: Effect Unit
  , notify :: String -> Maybe String -> Maybe String -> Aff Unit
  , openDirectoryPickerDialog :: Maybe (DirectoryPickerOptions -> Aff (Maybe (Array String)))
  , openFilePickerDialog :: Maybe (FilePickerOptions -> Aff (Maybe (Array String)))
  , saveFilePickerDialog :: Maybe (SaveFilePickerOptions -> Aff (Maybe String))
  , checkUpdate :: Maybe (Aff UpdateCheckResult)
  , update :: Maybe (Aff Unit)
  , customFetch :: Maybe (String -> Aff String)
  , getDefaultServerUrl :: Maybe (Aff (Maybe String))
  , setDefaultServerUrl :: Maybe (Maybe String -> Aff Unit)
  , parseMarkdown :: Maybe (String -> Aff String)
  }

-- | FFI imports for web platform
foreign import openLinkImpl :: String -> Effect Unit
foreign import restartImpl :: Aff Unit
foreign import backImpl :: Effect Unit
foreign import forwardImpl :: Effect Unit
foreign import notifyImpl :: String -> String -> String -> Aff Unit

-- | Create a minimal web platform
mkPlatform :: Platform
mkPlatform =
  { platformType: Web
  , os: Nothing
  , version: Nothing
  , openLink: openLinkImpl
  , restart: restartImpl
  , back: backImpl
  , forward: forwardImpl
  , notify: \title desc href ->
      let d = case desc of
                Just s -> s
                Nothing -> ""
          h = case href of
                Just s -> s
                Nothing -> ""
      in notifyImpl title d h
  , openDirectoryPickerDialog: Nothing
  , openFilePickerDialog: Nothing
  , saveFilePickerDialog: Nothing
  , checkUpdate: Nothing
  , update: Nothing
  , customFetch: Nothing
  , getDefaultServerUrl: Nothing
  , setDefaultServerUrl: Nothing
  , parseMarkdown: Nothing
  }

-- | Open a URL in the default browser
openLink :: forall m. MonadAff m => Platform -> String -> m Unit
openLink platform url = liftEffect (platform.openLink url)

-- | Restart the app
restart :: Platform -> Aff Unit
restart = _.restart

-- | Navigate back in history
back :: Platform -> Effect Unit
back = _.back

-- | Navigate forward in history
forward :: Platform -> Effect Unit
forward = _.forward

-- | Send a system notification
notify :: Platform -> String -> Maybe String -> Maybe String -> Aff Unit
notify platform title desc href = platform.notify title desc href

-- | Open directory picker dialog
openDirectoryPickerDialog :: Platform -> DirectoryPickerOptions -> Aff (Maybe (Array String))
openDirectoryPickerDialog platform opts =
  case platform.openDirectoryPickerDialog of
    Nothing -> pure Nothing
    Just fn -> fn opts

-- | Open file picker dialog
openFilePickerDialog :: Platform -> FilePickerOptions -> Aff (Maybe (Array String))
openFilePickerDialog platform opts =
  case platform.openFilePickerDialog of
    Nothing -> pure Nothing
    Just fn -> fn opts

-- | Save file picker dialog
saveFilePickerDialog :: Platform -> SaveFilePickerOptions -> Aff (Maybe String)
saveFilePickerDialog platform opts =
  case platform.saveFilePickerDialog of
    Nothing -> pure Nothing
    Just fn -> fn opts

-- | Check for updates
checkUpdate :: Platform -> Aff (Maybe UpdateCheckResult)
checkUpdate platform =
  case platform.checkUpdate of
    Nothing -> pure Nothing
    Just fn -> fn >>= \r -> pure (Just r)

-- | Install updates
update :: Platform -> Aff Unit
update platform =
  case platform.update of
    Nothing -> pure unit
    Just fn -> fn

-- | Get the configured default server URL
getDefaultServerUrl :: Platform -> Aff (Maybe String)
getDefaultServerUrl platform =
  case platform.getDefaultServerUrl of
    Nothing -> pure Nothing
    Just fn -> fn

-- | Set the default server URL
setDefaultServerUrl :: Platform -> Maybe String -> Aff Unit
setDefaultServerUrl platform url =
  case platform.setDefaultServerUrl of
    Nothing -> pure unit
    Just fn -> fn url

-- | Parse markdown to HTML
parseMarkdown :: Platform -> String -> Aff (Maybe String)
parseMarkdown platform md =
  case platform.parseMarkdown of
    Nothing -> pure Nothing
    Just fn -> fn md >>= \r -> pure (Just r)

-- | Get platform type
platformType :: Platform -> PlatformType
platformType = _.platformType

-- | Get operating system
os :: Platform -> Maybe OperatingSystem
os = _.os

-- | Get version
version :: Platform -> Maybe String
version = _.version

-- | Get custom fetch function
customFetch :: Platform -> Maybe (String -> Aff String)
customFetch = _.customFetch
