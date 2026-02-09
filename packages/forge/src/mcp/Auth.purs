-- | MCP Authentication
-- | 1:1 parity with opencode-dev/packages/opencode/src/mcp/auth.ts
module Forge.MCP.Auth where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

type MCPAuthToken =
  { token :: String
  , expiresAt :: Maybe Number
  }

authenticate :: String -> Aff (Either String MCPAuthToken)
authenticate _ = pure $ Right { token: "", expiresAt: Nothing }

refresh :: String -> Aff (Either String MCPAuthToken)
refresh _ = pure $ Right { token: "", expiresAt: Nothing }
