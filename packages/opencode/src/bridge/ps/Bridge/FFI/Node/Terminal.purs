-- | Terminal Execution FFI
module Bridge.FFI.Node.Terminal where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Terminal execute response
type TerminalExecuteResponse =
  { success :: Boolean
  , output :: Maybe String
  , exitCode :: Maybe Int
  }

-- | Execute terminal command
foreign import executeCommand :: String -> Maybe String -> Maybe String -> Aff (Either String TerminalExecuteResponse)