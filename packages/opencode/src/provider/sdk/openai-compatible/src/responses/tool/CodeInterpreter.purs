-- | Code Interpreter Tool
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/responses/tool/code-interpreter.ts
module Opencode.Provider.SDK.OpenAICompatible.Responses.Tool.CodeInterpreter where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Code interpreter input
type CodeInterpreterInput =
  { code :: String
  , language :: String
  }

-- | Code interpreter output
type CodeInterpreterOutput =
  { result :: String
  , logs :: Array String
  }

-- | Execute code
execute :: CodeInterpreterInput -> Aff (Either String CodeInterpreterOutput)
execute input = notImplemented "Tool.CodeInterpreter.execute"
