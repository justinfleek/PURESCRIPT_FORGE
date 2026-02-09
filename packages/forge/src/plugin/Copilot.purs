-- | Copilot plugin
-- | Ported from: opencode-dev/packages/opencode/src/plugin/copilot.ts
module Forge.Plugin.Copilot where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Copilot plugin configuration
type CopilotConfig =
  { enabled :: Boolean
  , apiKey :: Maybe String
  }

-- | Initialize the Copilot plugin
-- | Validates configuration and registers with the provider system
init :: CopilotConfig -> Aff (Either String Unit)
init config =
  if not config.enabled
    then pure $ Right unit
    else fromEffectFnAff (initCopilotFFI config)

-- | Check if Copilot is available
isAvailable :: Aff Boolean
isAvailable = fromEffectFnAff isAvailableFFI

-- | FFI: Initialize Copilot
foreign import initCopilotFFI :: CopilotConfig -> EffectFnAff (Either String Unit)

-- | FFI: Check availability
foreign import isAvailableFFI :: EffectFnAff Boolean
