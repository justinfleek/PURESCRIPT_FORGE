-- | TUI Attach functionality
-- | Ported from: opencode-dev/packages/forge/src/cli/cmd/tui/attach.ts
module Forge.CLI.Cmd.TUI.Attach where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Configuration for attaching to a remote server
type AttachConfig =
  { serverUrl :: String
  , sessionId :: String
  }

-- | Attach to a running forge server
-- | Establishes WebSocket connection to the server and synchronizes state
attach :: AttachConfig -> Aff (Either String Unit)
attach config = fromEffectFnAff (attachToServerFFI config)

-- | Detach from current server
detach :: Aff (Either String Unit)
detach = fromEffectFnAff detachFFI

-- | FFI: Attach to server via WebSocket
foreign import attachToServerFFI :: AttachConfig -> EffectFnAff (Either String Unit)

-- | FFI: Detach from server
foreign import detachFFI :: EffectFnAff (Either String Unit)
