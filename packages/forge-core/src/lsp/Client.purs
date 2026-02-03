-- | LSP Client
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/lsp/client.ts
module Forge.LSP.Client where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | LSP Client configuration
type LSPClientConfig =
  { serverPath :: String
  , workspaceRoot :: String
  , language :: String
  }

-- | LSP Client instance
type LSPClient =
  { config :: LSPClientConfig
  , isConnected :: Boolean
  }

-- | Create an LSP client
create :: LSPClientConfig -> Aff (Either String LSPClient)
create config = notImplemented "LSP.Client.create"

-- | Connect to LSP server
connect :: LSPClient -> Aff (Either String Unit)
connect client = notImplemented "LSP.Client.connect"

-- | Disconnect from LSP server
disconnect :: LSPClient -> Aff (Either String Unit)
disconnect client = notImplemented "LSP.Client.disconnect"
