-- | Session System - system prompt handling
-- |
-- | Provides system prompts based on model/provider type.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/system.ts
module Forge.Session.System
  ( instructions
  , provider
  , environment
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | Get Codex instructions prompt
foreign import instructions :: String

-- | Get provider-specific system prompts
foreign import provider :: Foreign -> Array String

-- | Get environment context prompt
foreign import environment :: Foreign -> Aff (Array String)
