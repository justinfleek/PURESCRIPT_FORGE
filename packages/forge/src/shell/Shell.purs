-- | Shell utilities
-- | 1:1 parity with opencode-dev/packages/opencode/src/shell/shell.ts
module Forge.Shell.Shell where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

type ShellResult =
  { stdout :: String
  , stderr :: String
  , exitCode :: Int
  }

foreign import execFFI :: String -> Maybe String -> Aff (Either String ShellResult)
foreign import getDefaultShellFFI :: Aff String
foreign import escapeFFI :: String -> String

exec :: String -> Maybe String -> Aff (Either String ShellResult)
exec command cwd = execFFI command cwd

getDefaultShell :: Aff String
getDefaultShell = getDefaultShellFFI

escape :: String -> String
escape = escapeFFI
