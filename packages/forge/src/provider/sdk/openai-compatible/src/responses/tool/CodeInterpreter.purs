-- | Code Interpreter Tool
-- | Ported from: code-interpreter.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.CodeInterpreter where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

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

-- | Execute code via language-specific interpreter
execute :: CodeInterpreterInput -> Aff (Either String CodeInterpreterOutput)
execute input = fromEffectFnAff (executeCodeFFI input.code input.language)

-- | FFI for code execution
foreign import executeCodeFFI :: String -> String -> EffectFnAff (Either String CodeInterpreterOutput)
