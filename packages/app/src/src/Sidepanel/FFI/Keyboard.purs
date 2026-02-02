-- | Keyboard shortcuts FFI bindings
module Sidepanel.FFI.Keyboard where

import Prelude
import Effect (Effect)

-- | Set up keyboard shortcuts for code selection
-- |
-- | - Ctrl+C / Cmd+C: Copy selected code
-- | - Ctrl+Enter / Cmd+Enter: Add selected code to chat
foreign import setupKeyboardShortcuts :: Effect Unit -> Effect Unit -> Effect (Effect Unit)
