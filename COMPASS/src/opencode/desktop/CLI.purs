-- | Desktop CLI - Install CLI command
-- | Phase 5: Desktop/Web Migration
module Opencode.Desktop.CLI where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Map as Map
import Opencode.Desktop.I18n as I18n
import Opencode.Desktop.FFI.Tauri as Tauri

-- | Install CLI command
installCLI :: Aff Unit
installCLI = do
  -- Initialize i18n
  I18n.initI18n
  
  -- Invoke Tauri command to install CLI
  result <- Tauri.invokeInstallCLI # liftEffect
  
  case result of
    Left err -> do
      -- Show error message
      let errorParams = Map.singleton "error" err
      message <- I18n.t "desktop.cli.failed.message" errorParams
      title <- I18n.t "desktop.cli.failed.title" Map.empty
      Tauri.showMessage message { title } # liftEffect
    Right path -> do
      -- Show success message
      let pathParams = Map.singleton "path" path
      message <- I18n.t "desktop.cli.installed.message" pathParams
      title <- I18n.t "desktop.cli.installed.title" Map.empty
      Tauri.showMessage message { title } # liftEffect
