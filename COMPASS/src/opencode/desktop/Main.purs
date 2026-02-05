-- | Desktop - Tauri desktop application entry point
-- | Phase 5: Desktop/Web Migration
module Opencode.Desktop.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Opencode.Desktop.CLI as CLI
import Opencode.Desktop.Menu as Menu
import Opencode.Desktop.Updater as Updater
import Opencode.Desktop.I18n as I18n

-- | Initialize desktop application
init :: Effect Unit
init = launchAff_ do
  -- Initialize internationalization
  I18n.initI18n
  
  -- Create application menu
  Menu.createMenu
  
  -- Setup webview zoom handler
  setupWebviewZoom
  
  -- Check for updates on startup (silent)
  Updater.runUpdater { alertOnFail: false }

-- | Setup webview zoom handling
-- | Tauri's webview plugin handles zoom automatically via keyboard shortcuts
-- | (Cmd/Ctrl + -/=/0) and persists zoom level automatically
-- | No additional implementation needed beyond Tauri's built-in functionality
setupWebviewZoom :: Aff Unit
setupWebviewZoom = pure unit
