-- | Local Shell Tool
-- | Ported from: local-shell.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.LocalShell where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

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
execute input = fromEffectFnAff (executeShellFFI input.command input.cwd input.timeout)

-- | FFI for shell command execution via child_process
foreign import executeShellFFI :: String -> Maybe String -> Maybe Int -> EffectFnAff (Either String LocalShellOutput)
