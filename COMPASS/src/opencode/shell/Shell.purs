-- | Shell utilities
module Opencode.Shell.Shell where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Bridge.FFI.Node.Terminal as Terminal

-- | Shell execution result
type ShellResult =
  { stdout :: String
  , stderr :: String
  , exitCode :: Int
  }

-- | Execute a shell command
exec :: String -> Maybe String -> Aff (Either String ShellResult)
exec command cwd = do
  result <- Terminal.executeCommand command cwd Nothing
  case result of
    Left err -> pure $ Left err
    Right resp -> pure $ Right
      { stdout: fromMaybe "" resp.output
      , stderr: ""
      , exitCode: fromMaybe 0 resp.exitCode
      }

-- | Get the default shell
getDefaultShell :: Aff String
getDefaultShell = do
  shell <- liftEffect getSystemShell
  pure shell
  where
    foreign import getSystemShell :: Effect String

-- | Escape a string for shell
-- | Escapes special characters for safe shell usage
escape :: String -> String
escape str =
  -- Escape single quotes by replacing ' with '\''
  -- Wrap entire string in single quotes for safety
  "'" <> String.replaceAll (String.Pattern "'") (String.Replacement "'\\''") str <> "'"
