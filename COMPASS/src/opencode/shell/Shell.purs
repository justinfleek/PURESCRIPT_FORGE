-- | Shell utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/shell/shell.ts
module Opencode.Shell.Shell where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Shell execution result
type ShellResult =
  { stdout :: String
  , stderr :: String
  , exitCode :: Int
  }

-- | Execute a shell command
exec :: String -> Maybe String -> Aff (Either String ShellResult)
exec command cwd = notImplemented "Shell.Shell.exec"

-- | Get the default shell
getDefaultShell :: Aff String
getDefaultShell = notImplemented "Shell.Shell.getDefaultShell"

-- | Escape a string for shell
escape :: String -> String
escape str = str -- TODO: Implement proper escaping
