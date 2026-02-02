-- | TUI Editor utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/util/editor.ts
module Opencode.CLI.Cmd.TUI.Util.Editor where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Open a file in the user's preferred editor
openInEditor :: String -> Aff (Either String Unit)
openInEditor path = notImplemented "CLI.Cmd.TUI.Util.Editor.openInEditor"

-- | Get the default editor command
getEditorCommand :: Aff (Maybe String)
getEditorCommand = notImplemented "CLI.Cmd.TUI.Util.Editor.getEditorCommand"
