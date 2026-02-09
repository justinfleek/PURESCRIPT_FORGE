-- | Installation management
-- |
-- | Handles version checking, upgrades, and installation method detection.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/installation/index.ts
module Forge.Installation.Index
  ( Info
  , Method
  , event
  , info
  , isPreview
  , isLocal
  , method
  , upgrade
  , latest
  , version
  , channel
  , userAgent
  , upgradeFailedError
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | Installation info
type Info =
  { version :: String
  , latest :: String
  }

-- | Installation method type
type Method = String  -- "curl" | "npm" | "yarn" | "pnpm" | "bun" | "brew" | "scoop" | "choco" | "unknown"

-- | Installation events
foreign import event :: Foreign

-- | Get installation info
foreign import info :: Aff Info

-- | Check if running preview channel
foreign import isPreview :: Boolean

-- | Check if running local build
foreign import isLocal :: Boolean

-- | Detect installation method
foreign import method :: Aff Method

-- | Upgrade to target version
foreign import upgrade :: Method -> String -> Aff Unit

-- | Get latest version for installation method
foreign import latest :: Method -> Aff String

-- | Current version
foreign import version :: String

-- | Current channel
foreign import channel :: String

-- | User agent string
foreign import userAgent :: String

-- | Error when upgrade fails
foreign import upgradeFailedError :: Foreign
