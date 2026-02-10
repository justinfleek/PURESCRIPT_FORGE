-- | Terminal Execution FFI
module Bridge.FFI.Node.Terminal where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Terminal execute response
type TerminalExecuteResponse =
  { success :: Boolean
  , output :: Maybe String
  , exitCode :: Maybe Int
  }

-- | FFI implementation
foreign import executeCommandImpl :: String -> Maybe String -> Maybe String -> EffectFnAff (Either String TerminalExecuteResponse)

-- | Execute terminal command
executeCommand :: String -> Maybe String -> Maybe String -> Aff (Either String TerminalExecuteResponse)
executeCommand cmd cwd sessionId =
  fromEffectFnAff $ executeCommandImpl cmd cwd sessionId
