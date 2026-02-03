-- | Stats command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/stats.ts
module Forge.CLI.Cmd.Stats where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type StatsArgs =
  { period :: Maybe String  -- day, week, month
  , format :: Maybe String  -- table, json
  }

-- | Execute the stats command
execute :: StatsArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Stats.execute"
