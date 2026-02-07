-- | Window FFI Module - Window Dimensions and Viewport
-- |
-- | **What:** Provides FFI bindings for getting window/viewport dimensions.
-- | **Why:** Enables responsive layout detection and viewport-based rendering decisions.
-- | **How:** Uses foreign function imports to access window.innerWidth and window.innerHeight.
module Sidepanel.FFI.Window where

import Prelude
import Effect (Effect)

-- | Get viewport width in pixels
foreign import getViewportWidth :: Effect Number

-- | Get viewport height in pixels
foreign import getViewportHeight :: Effect Number
