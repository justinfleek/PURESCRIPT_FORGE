-- | IDE Integration
-- | Ported from: opencode-dev/packages/opencode/src/ide/index.ts
module Forge.IDE.Index where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Supported IDE types
data IDEType = VSCode | Cursor | JetBrains | Vim | Emacs | Unknown

instance showIDEType :: Show IDEType where
  show VSCode = "vscode"
  show Cursor = "cursor"
  show JetBrains = "jetbrains"
  show Vim = "vim"
  show Emacs = "emacs"
  show Unknown = "unknown"

-- | Detect the current IDE from environment
detect :: Aff (Maybe IDEType)
detect = fromEffectFnAff detectIDEFFI

-- | Open a file in the detected IDE
openFile :: String -> Maybe Int -> Aff (Either String Unit)
openFile filePath line = fromEffectFnAff (openFileInIDEFFI filePath line)

-- | FFI: Detect IDE
foreign import detectIDEFFI :: EffectFnAff (Maybe IDEType)

-- | FFI: Open file in IDE
foreign import openFileInIDEFFI :: String -> Maybe Int -> EffectFnAff (Either String Unit)
