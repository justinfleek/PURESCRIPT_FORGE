-- | Clipboard FFI bindings
-- |
-- | Provides functions for copying text to clipboard, reading from clipboard,
-- | and getting text selection.
module Sidepanel.FFI.Clipboard
  ( copyToClipboard
  , getSelection
  , readFromClipboard
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Control.Promise (Promise, toAff)
import Data.Maybe (Maybe)

-- | Copy text to clipboard
-- | Uses modern Clipboard API with fallback to execCommand for older browsers
foreign import copyToClipboard :: String -> Effect Unit

-- | Get currently selected text from window
-- | Returns Nothing if no selection or selection is collapsed
foreign import getSelection :: Effect (Maybe String)

-- | Read text content from clipboard
-- | Uses navigator.clipboard.readText() API
-- | Requires clipboard-read permission in browser
readFromClipboard :: Aff String
readFromClipboard = toAff =<< liftEffect readFromClipboardImpl

foreign import readFromClipboardImpl :: Effect (Promise String)
