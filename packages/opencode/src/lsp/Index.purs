-- | LSP Index - main entry point
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/lsp/index.ts
module Opencode.LSP.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Initialize LSP
init :: String -> Aff (Either String Unit)
init workspaceRoot = notImplemented "LSP.Index.init"

-- | Get diagnostics for a file
getDiagnostics :: String -> Aff (Either String (Array String))
getDiagnostics filePath = notImplemented "LSP.Index.getDiagnostics"

-- | Get hover info
getHover :: String -> Int -> Int -> Aff (Either String String)
getHover filePath line column = notImplemented "LSP.Index.getHover"

-- | Get completions
getCompletions :: String -> Int -> Int -> Aff (Either String (Array String))
getCompletions filePath line column = notImplemented "LSP.Index.getCompletions"
