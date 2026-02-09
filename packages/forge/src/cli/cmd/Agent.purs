-- | Agent management command
module Forge.CLI.Cmd.Agent where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

type AgentArgs =
  { list :: Boolean
  , info :: Maybe String
  }

foreign import listAgentsFFI :: Aff (Either String (Array String))
foreign import showAgentInfoFFI :: String -> Aff (Either String Unit)
foreign import printLinesFFI :: Array String -> Aff Unit

-- | Execute the agent command
execute :: AgentArgs -> Aff (Either String Unit)
execute args = case args.info of
  Just name -> showAgentInfoFFI name
  Nothing -> do
    result <- listAgentsFFI
    case result of
      Left err -> pure $ Left err
      Right agents -> do
        printLinesFFI agents
        pure $ Right unit

-- | List available agents
listAgents :: Aff (Either String (Array String))
listAgents = listAgentsFFI
