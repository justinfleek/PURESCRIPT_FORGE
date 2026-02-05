-- | Sound FFI Module - Alert Sound Effects
-- |
-- | **What:** Provides FFI bindings for playing alert sounds when critical alerts are triggered.
-- | **Why:** Provides audio feedback for critical alerts, improving user awareness of important
-- |         events even when not looking at the screen.
-- | **How:** Uses Web Audio API to generate alert sounds (beeps) when alerts are shown.
-- |
-- | **Dependencies:** None (pure FFI bindings)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.Sound as Sound
-- |
-- | -- Play alert sound
-- | liftEffect Sound.playAlertSound
-- | ```
module Sidepanel.FFI.Sound where

import Prelude
import Effect (Effect)

-- | Play alert sound - Plays a beep sound for alert notifications
foreign import playAlertSound :: Effect Unit
