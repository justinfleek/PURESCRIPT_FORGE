-- | Local Shell Tool
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/responses/tool/local-shell.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.LocalShell where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Local shell input
type LocalShellInput =
  { command :: String
  , cwd :: Maybe String
  , timeout :: Maybe Int
  }

-- | Local shell output
type LocalShellOutput =
  { stdout :: String
  , stderr :: String
  , exitCode :: Int
  }

-- | Execute a shell command
execute :: LocalShellInput -> Aff (Either String LocalShellOutput)
execute input = notImplemented "Tool.LocalShell.execute"
