-- | Session Status
-- |
-- | Tracks session busy/idle/retry states.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/status.ts
module Forge.Session.Status
  ( Info
  , event
  , get
  , list
  , set
  ) where

import Prelude
import Foreign (Foreign)
import Foreign.Object (Object)

-- | Session status info (union type)
-- | { type: "idle" } | { type: "busy" } | { type: "retry", attempt, message, next }
type Info = Foreign

-- | Status events
foreign import event :: Foreign

-- | Get status for session
foreign import get :: String -> Info

-- | Get all session statuses
foreign import list :: Object Info

-- | Set status for session
foreign import set :: String -> Info -> Unit
