-- | Debug Skill command
module Forge.CLI.Cmd.Debug.Skill where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

foreign import debugSkillFFI :: String -> Aff (Either String Unit)

-- | Execute debug skill command
execute :: Maybe String -> Aff (Either String Unit)
execute skillName = do
  let name = case skillName of
        Just s -> s
        Nothing -> ""
  debugSkillFFI name
