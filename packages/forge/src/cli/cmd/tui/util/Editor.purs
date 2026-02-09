-- | TUI Editor utilities
-- | Ported from COMPASS reference: opencode/cli/cmd/tui/util/Editor.purs
module Forge.CLI.Cmd.TUI.Util.Editor where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Open a file in the user's preferred editor
openInEditor :: String -> Aff (Either String Unit)
openInEditor filePath = fromEffectFnAff (openInEditorFFI filePath)

-- | Open a file at a specific line in the user's preferred editor
openInEditorAtLine :: String -> Int -> Aff (Either String Unit)
openInEditorAtLine filePath line = fromEffectFnAff (openInEditorAtLineFFI filePath line)

-- | Get the default editor command
getEditorCommand :: Aff (Maybe String)
getEditorCommand = fromEffectFnAff getEditorCommandFFI

-- | FFI: Open file in editor
foreign import openInEditorFFI :: String -> EffectFnAff (Either String Unit)

-- | FFI: Open file in editor at line
foreign import openInEditorAtLineFFI :: String -> Int -> EffectFnAff (Either String Unit)

-- | FFI: Get editor command
foreign import getEditorCommandFFI :: EffectFnAff (Maybe String)
