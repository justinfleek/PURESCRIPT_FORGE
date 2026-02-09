-- | TUI Clipboard utilities
-- | Ported from COMPASS reference: opencode/cli/cmd/tui/util/Clipboard.purs
module Forge.CLI.Cmd.TUI.Util.Clipboard where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Copy text to clipboard
copy :: String -> Aff (Either String Unit)
copy text = fromEffectFnAff (copyToClipboardFFI text)

-- | Read from clipboard
paste :: Aff (Either String String)
paste = fromEffectFnAff pasteFromClipboardFFI

-- | FFI: Copy text to system clipboard
foreign import copyToClipboardFFI :: String -> EffectFnAff (Either String Unit)

-- | FFI: Read text from system clipboard
foreign import pasteFromClipboardFFI :: EffectFnAff (Either String String)
