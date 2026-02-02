-- | TUI Directory context
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/context/directory.ts
module Opencode.CLI.Cmd.TUI.Context.Directory where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Directory context for TUI
type DirectoryContext =
  { cwd :: String
  , projectRoot :: String
  , gitRoot :: String
  }

-- | Get current directory context
getContext :: Aff (Either String DirectoryContext)
getContext = notImplemented "CLI.Cmd.TUI.Context.Directory.getContext"

-- | Change directory
changeDirectory :: String -> Aff (Either String Unit)
changeDirectory path = notImplemented "CLI.Cmd.TUI.Context.Directory.changeDirectory"
