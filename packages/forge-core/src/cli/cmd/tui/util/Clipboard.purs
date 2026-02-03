-- | TUI Clipboard utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/util/clipboard.ts
module Forge.CLI.Cmd.TUI.Util.Clipboard where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Copy text to clipboard
copy :: String -> Aff (Either String Unit)
copy text = notImplemented "CLI.Cmd.TUI.Util.Clipboard.copy"

-- | Read from clipboard
paste :: Aff (Either String String)
paste = notImplemented "CLI.Cmd.TUI.Util.Clipboard.paste"
