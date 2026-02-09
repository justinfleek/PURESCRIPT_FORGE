-- | TUI Directory context
-- | Ported from COMPASS reference: opencode/cli/cmd/tui/context/Directory.purs
module Forge.CLI.Cmd.TUI.Context.Directory where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Directory context for TUI
type DirectoryContext =
  { cwd :: String
  , projectRoot :: String
  , gitRoot :: String
  }

-- | Get current directory context
getContext :: Aff (Either String DirectoryContext)
getContext = fromEffectFnAff getDirectoryContextFFI

-- | Change directory
changeDirectory :: String -> Aff (Either String Unit)
changeDirectory dir = fromEffectFnAff (changeDirectoryFFI dir)

-- | FFI: Get directory context
foreign import getDirectoryContextFFI :: EffectFnAff (Either String DirectoryContext)

-- | FFI: Change working directory
foreign import changeDirectoryFFI :: String -> EffectFnAff (Either String Unit)
