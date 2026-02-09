-- | Debug command index
module Forge.CLI.Cmd.Debug.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

-- | Debug command types
data DebugCommand
  = DebugAgent
  | DebugConfig
  | DebugFile
  | DebugLsp
  | DebugRipgrep
  | DebugScrap
  | DebugSkill
  | DebugSnapshot

foreign import showHelpFFI :: Aff Unit

-- | Execute debug command
execute :: DebugCommand -> Aff (Either String Unit)
execute cmd = do
  showHelpFFI
  pure $ Right unit
