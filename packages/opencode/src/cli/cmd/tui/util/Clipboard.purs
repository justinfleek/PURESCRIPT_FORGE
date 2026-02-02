-- | TUI Clipboard utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/util/clipboard.ts
module Opencode.CLI.Cmd.TUI.Util.Clipboard where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Copy text to clipboard
copy :: String -> Aff (Either String Unit)
copy text = notImplemented "CLI.Cmd.TUI.Util.Clipboard.copy"

-- | Read from clipboard
paste :: Aff (Either String String)
paste = notImplemented "CLI.Cmd.TUI.Util.Clipboard.paste"
