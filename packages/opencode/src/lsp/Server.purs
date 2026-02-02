-- | LSP Server management
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/lsp/server.ts
module Opencode.LSP.Server where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | LSP Server info
type LSPServer =
  { language :: String
  , command :: String
  , args :: Array String
  , isRunning :: Boolean
  }

-- | Start an LSP server
start :: String -> Aff (Either String LSPServer)
start language = notImplemented "LSP.Server.start"

-- | Stop an LSP server
stop :: String -> Aff (Either String Unit)
stop language = notImplemented "LSP.Server.stop"

-- | Check if server is running
isRunning :: String -> Aff Boolean
isRunning language = notImplemented "LSP.Server.isRunning"
