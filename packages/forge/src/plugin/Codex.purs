-- | Codex plugin
-- | Ported from: opencode-dev/packages/opencode/src/plugin/codex.ts
module Forge.Plugin.Codex where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Codex plugin configuration
type CodexConfig =
  { enabled :: Boolean
  , apiKey :: Maybe String
  }

-- | Initialize the Codex plugin
-- | Validates configuration and registers with the provider system
init :: CodexConfig -> Aff (Either String Unit)
init config =
  if not config.enabled
    then pure $ Right unit
    else fromEffectFnAff (initCodexFFI config)

-- | Check if Codex is available
isAvailable :: Aff Boolean
isAvailable = fromEffectFnAff isAvailableFFI

-- | FFI: Initialize Codex
foreign import initCodexFFI :: CodexConfig -> EffectFnAff (Either String Unit)

-- | FFI: Check availability
foreign import isAvailableFFI :: EffectFnAff Boolean
