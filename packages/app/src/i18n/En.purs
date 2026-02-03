-- | English translations (base language)
-- | Migrated from forge-dev/packages/app/src/i18n/en.ts
module Forge.App.I18n.En (dict) where

import Foreign.Object (Object, fromFoldable)
import Data.Tuple (Tuple(..))

dict :: Object String
dict = fromFoldable
  -- Command categories
  [ Tuple "command.category.suggested" "Suggested"
  , Tuple "command.category.view" "View"
  , Tuple "command.category.project" "Project"
  , Tuple "command.category.provider" "Provider"
  , Tuple "command.category.server" "Server"
  , Tuple "command.category.session" "Session"
  , Tuple "command.category.theme" "Theme"
  , Tuple "command.category.language" "Language"
  , Tuple "command.category.file" "File"
  , Tuple "command.category.context" "Context"
  , Tuple "command.category.terminal" "Terminal"
  , Tuple "command.category.model" "Model"
  , Tuple "command.category.mcp" "MCP"
  , Tuple "command.category.agent" "Agent"
  , Tuple "command.category.permissions" "Permissions"
  , Tuple "command.category.workspace" "Workspace"
  , Tuple "command.category.settings" "Settings"
  
  -- Theme
  , Tuple "theme.scheme.system" "System"
  , Tuple "theme.scheme.light" "Light"
  , Tuple "theme.scheme.dark" "Dark"
  
  -- Commands
  , Tuple "command.sidebar.toggle" "Toggle sidebar"
  , Tuple "command.project.open" "Open project"
  , Tuple "command.provider.connect" "Connect provider"
  , Tuple "command.server.switch" "Switch server"
  , Tuple "command.settings.open" "Open settings"
  , Tuple "command.session.previous" "Previous session"
  , Tuple "command.session.next" "Next session"
  , Tuple "command.session.archive" "Archive session"
  , Tuple "command.palette" "Command palette"
  , Tuple "command.session.new" "New session"
  , Tuple "command.file.open" "Open file"
  , Tuple "command.terminal.toggle" "Toggle terminal"
  , Tuple "command.model.choose" "Choose model"
  
  -- Common
  , Tuple "common.search.placeholder" "Search"
  , Tuple "common.goBack" "Back"
  , Tuple "common.goForward" "Forward"
  , Tuple "common.loading" "Loading"
  , Tuple "common.cancel" "Cancel"
  , Tuple "common.connect" "Connect"
  , Tuple "common.disconnect" "Disconnect"
  , Tuple "common.submit" "Submit"
  , Tuple "common.save" "Save"
  , Tuple "common.default" "Default"
  , Tuple "common.close" "Close"
  , Tuple "common.edit" "Edit"
  , Tuple "common.delete" "Delete"
  
  -- Prompt
  , Tuple "prompt.placeholder.normal" "Ask anything..."
  , Tuple "prompt.action.send" "Send"
  , Tuple "prompt.action.stop" "Stop"
  , Tuple "prompt.voice.start" "Voice input"
  , Tuple "prompt.voice.stop" "Stop recording"
  , Tuple "prompt.voice.processing" "Processing..."
  
  -- Languages
  , Tuple "language.en" "English"
  , Tuple "language.zh" "简体中文"
  , Tuple "language.zht" "繁體中文"
  , Tuple "language.ko" "한국어"
  , Tuple "language.de" "Deutsch"
  , Tuple "language.es" "Español"
  , Tuple "language.fr" "Français"
  , Tuple "language.da" "Dansk"
  , Tuple "language.ja" "日本語"
  , Tuple "language.pl" "Polski"
  , Tuple "language.ru" "Русский"
  , Tuple "language.ar" "العربية"
  , Tuple "language.no" "Norsk"
  , Tuple "language.br" "Português (Brasil)"
  , Tuple "language.th" "ไทย"
  
  -- Error
  , Tuple "error.page.title" "Something went wrong"
  , Tuple "error.chain.unknown" "Unknown error"
  
  -- Session
  , Tuple "session.tab.session" "Session"
  , Tuple "session.tab.review" "Review"
  , Tuple "session.tab.context" "Context"
  , Tuple "session.messages.loading" "Loading messages..."
  
  -- Settings
  , Tuple "settings.tab.general" "General"
  , Tuple "settings.tab.shortcuts" "Shortcuts"
  
  -- Terminal
  , Tuple "terminal.title" "Terminal"
  , Tuple "terminal.loading" "Loading terminal..."
  ]
