-- | Lsp.purs - Language Server Protocol tool
-- | TODO: Implement - mirrors opencode/src/tool/lsp.ts
module Tool.Lsp where

import Prelude
import Effect.Aff (Aff)

type Params = { action :: String, file :: String }
type Result = { title :: String, output :: String }

execute :: Params -> Aff Result
execute _ = notImplemented "Tool.Lsp.execute"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
