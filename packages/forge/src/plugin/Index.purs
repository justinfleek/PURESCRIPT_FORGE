-- | Plugin system
-- |
-- | Loads and manages plugins, triggers plugin hooks.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/plugin/index.ts
module Forge.Plugin.Index
  ( trigger
  , list
  , init
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | Trigger a plugin hook
-- | name: hook name, input: hook input, output: initial output
-- | Returns modified output after all plugins process it
foreign import trigger :: forall input output. String -> input -> output -> Aff output

-- | List all loaded plugin hooks
foreign import list :: Aff (Array Foreign)

-- | Initialize plugin system
foreign import init :: Aff Unit
