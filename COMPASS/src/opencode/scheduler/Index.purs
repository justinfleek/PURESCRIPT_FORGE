-- | Task Scheduler
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/scheduler/index.ts
module Opencode.Scheduler.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Scheduled task
type ScheduledTask =
  { id :: String
  , name :: String
  , cron :: String
  , enabled :: Boolean
  }

-- | Schedule a task
schedule :: ScheduledTask -> Aff (Either String Unit)
schedule task = notImplemented "Scheduler.Index.schedule"

-- | Cancel a task
cancel :: String -> Aff (Either String Unit)
cancel taskId = notImplemented "Scheduler.Index.cancel"

-- | List scheduled tasks
list :: Aff (Either String (Array ScheduledTask))
list = notImplemented "Scheduler.Index.list"
