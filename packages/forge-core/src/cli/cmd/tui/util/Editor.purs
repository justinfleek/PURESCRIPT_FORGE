-- | TUI Editor utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/util/editor.ts
module Forge.CLI.Cmd.TUI.Util.Editor where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Open a file in the user's preferred editor
openInEditor :: String -> Aff (Either String Unit)
openInEditor path = notImplemented "CLI.Cmd.TUI.Util.Editor.openInEditor"

-- | Get the default editor command
getEditorCommand :: Aff (Maybe String)
getEditorCommand = notImplemented "CLI.Cmd.TUI.Util.Editor.getEditorCommand"
