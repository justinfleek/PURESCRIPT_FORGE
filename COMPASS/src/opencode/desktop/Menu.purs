-- | Desktop Menu - Create application menu
-- | Phase 5: Desktop/Web Migration
module Opencode.Desktop.Menu where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Data.Array as Array
import Opencode.Desktop.I18n as I18n
import Opencode.Desktop.FFI.Tauri as Tauri
import Opencode.Desktop.CLI as CLI
import Opencode.Desktop.Updater as Updater

-- | Create application menu (macOS only)
createMenu :: Aff Unit
createMenu = do
  -- Initialize i18n
  I18n.initI18n
  
  -- Check if macOS
  osType <- Tauri.getOSType # liftEffect
  if osType /= "macos"
    then pure unit
    else do
      -- Create menu items
      opencodeMenu <- createOpenCodeMenu
      editMenu <- createEditMenu
      
      -- Create menu
      Tauri.createMenu [opencodeMenu, editMenu] # liftEffect
      
      -- Set as app menu
      Tauri.setAsAppMenu # liftEffect

-- | Create OpenCode submenu
createOpenCodeMenu :: Aff Tauri.MenuItem
createOpenCodeMenu = do
  checkUpdatesText <- I18n.t "desktop.menu.checkForUpdates" Map.empty
  installCliText <- I18n.t "desktop.menu.installCli" Map.empty
  reloadText <- I18n.t "desktop.menu.reloadWebview" Map.empty
  restartText <- I18n.t "desktop.menu.restart" Map.empty
  
  updaterEnabled <- Updater.isUpdaterEnabled
  
  let items = Array.catMaybes
        [ Just $ Tauri.predefinedMenuItem "About"
        , if updaterEnabled
            then Just $ Tauri.menuItem checkUpdatesText (Updater.runUpdater { alertOnFail: true })
            else Nothing
        , Just $ Tauri.menuItem installCliText CLI.installCLI
        , Just $ Tauri.menuItem reloadText reloadWebview
        , Just $ Tauri.menuItem restartText restartApp
        , Just $ Tauri.predefinedMenuItem "Separator"
        , Just $ Tauri.predefinedMenuItem "Hide"
        , Just $ Tauri.predefinedMenuItem "HideOthers"
        , Just $ Tauri.predefinedMenuItem "ShowAll"
        , Just $ Tauri.predefinedMenuItem "Separator"
        , Just $ Tauri.predefinedMenuItem "Quit"
        ]
  
  Tauri.createSubmenu "OpenCode" items # liftEffect

-- | Create Edit submenu
createEditMenu :: Aff Tauri.MenuItem
createEditMenu = do
  let items =
        [ Tauri.predefinedMenuItem "Undo"
        , Tauri.predefinedMenuItem "Redo"
        , Tauri.predefinedMenuItem "Separator"
        , Tauri.predefinedMenuItem "Cut"
        , Tauri.predefinedMenuItem "Copy"
        , Tauri.predefinedMenuItem "Paste"
        , Tauri.predefinedMenuItem "SelectAll"
        ]
  
  Tauri.createSubmenu "Edit" items # liftEffect

-- | Reload webview
reloadWebview :: Aff Unit
reloadWebview = do
  Tauri.reloadWebview # liftEffect

-- | Restart application
restartApp :: Aff Unit
restartApp = do
  Tauri.killSidecar # liftEffect
  Tauri.relaunch # liftEffect
