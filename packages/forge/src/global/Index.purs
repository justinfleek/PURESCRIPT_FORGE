-- | Global state and paths
-- | 1:1 parity with opencode-dev/packages/opencode/src/global/global.ts
module Forge.Global.Index where

import Prelude
import Data.Maybe (Maybe)

-- | Path configuration
type PathInfo =
  { data :: String
  , config :: String
  , worktree :: String
  , directory :: String
  , state :: String
  , cache :: String
  , logs :: String
  }

-- | Get global paths
foreign import pathFFI :: PathInfo

-- | Ensure directories exist
foreign import ensureDirectoriesFFI :: Unit -> Unit
