-- | Desktop Updater - Check for and install updates
-- | Phase 5: Desktop/Web Migration
module Opencode.Desktop.Updater where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Opencode.Desktop.I18n as I18n
import Opencode.Desktop.FFI.Tauri as Tauri

-- | Check if updater is enabled
isUpdaterEnabled :: Boolean
isUpdaterEnabled = getUpdaterEnabled

-- | Run updater check and installation
runUpdater :: { alertOnFail :: Boolean } -> Aff Unit
runUpdater { alertOnFail } = do
  I18n.initI18n
  
  -- Check for updates
  updateResult <- Tauri.checkForUpdates # liftEffect
  
  case updateResult of
    Left _ -> do
      if alertOnFail
        then do
          message <- I18n.t "desktop.updater.checkFailed.message" Map.empty
          title <- I18n.t "desktop.updater.checkFailed.title" Map.empty
          Tauri.showMessage message { title } # liftEffect
        else pure unit
    Right Nothing -> do
      if alertOnFail
        then do
          message <- I18n.t "desktop.updater.none.message" Map.empty
          title <- I18n.t "desktop.updater.none.title" Map.empty
          Tauri.showMessage message { title } # liftEffect
        else pure unit
    Right (Just update) -> do
      -- Download update
      downloadResult <- Tauri.downloadUpdate update
      case downloadResult of
        Left _ -> do
          if alertOnFail
            then do
              message <- I18n.t "desktop.updater.downloadFailed.message" Map.empty
              title <- I18n.t "desktop.updater.downloadFailed.title" Map.empty
              Tauri.showMessage message { title } # liftEffect
            else pure unit
        Right _ -> do
          -- Ask user if they want to install
          let version = Tauri.getUpdateVersion update
          let versionParams = Map.singleton "version" version
          prompt <- I18n.t "desktop.updater.downloaded.prompt" versionParams
          title <- I18n.t "desktop.updater.downloaded.title" Map.empty
          shouldUpdate <- Tauri.ask prompt { title }
          
          if shouldUpdate
            then do
              -- Install update
              osType <- Tauri.getOSType # liftEffect
              if osType == "windows"
                then Tauri.killSidecar # liftEffect
                else pure unit
              
              installResult <- Tauri.installUpdate update
              case installResult of
                Left _ -> do
                  message <- I18n.t "desktop.updater.installFailed.message" Map.empty
                  title <- I18n.t "desktop.updater.installFailed.title" Map.empty
                  Tauri.showMessage message { title } # liftEffect
                Right _ -> do
                  Tauri.killSidecar # liftEffect
                  Tauri.relaunch # liftEffect
            else pure unit

-- | Get updater enabled status from window global
foreign import getUpdaterEnabled :: Boolean
