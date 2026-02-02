-- | Clipboard FFI bindings
-- |
-- | Provides functions for copying text to clipboard and reading selection
module Sidepanel.FFI.Clipboard where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)

-- | Copy text to clipboard
-- |
-- | Uses modern Clipboard API with fallback to execCommand for older browsers
foreign import copyToClipboard :: String -> Effect Unit

-- | Get currently selected text from window
-- |
-- | Returns Nothing if no selection or selection is collapsed
foreign import getSelection :: Effect (Maybe String)
