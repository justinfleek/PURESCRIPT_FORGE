-- | Bun process utilities
-- |
-- | Runs Bun commands and manages package installation in cache.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/bun/index.ts
module Forge.Bun.Index
  ( run
  , which
  , install
  , installFailedError
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)
import Data.Maybe (Maybe)

-- | Run a Bun command with options
-- | Returns spawn result on success, throws on non-zero exit
foreign import run :: Array String -> Maybe Foreign -> Aff Foreign

-- | Get path to current Bun executable
foreign import which :: String

-- | Install a package to global cache
-- | Uses lock to ensure only one install at a time
foreign import install :: String -> String -> Aff String

-- | Error thrown when package install fails
foreign import installFailedError :: Foreign
