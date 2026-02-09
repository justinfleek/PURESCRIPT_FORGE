-- | Task Scheduler
-- | Ported from: opencode-dev/packages/opencode/src/scheduler/index.ts
module Forge.Scheduler.Index where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Scheduled task definition
type ScheduledTask =
  { id :: String
  , name :: String
  , cron :: String
  , enabled :: Boolean
  }

-- | Schedule a task
schedule :: ScheduledTask -> Aff (Either String Unit)
schedule task = fromEffectFnAff (scheduleFFI task)

-- | Cancel a scheduled task by ID
cancel :: String -> Aff (Either String Unit)
cancel taskId = fromEffectFnAff (cancelFFI taskId)

-- | List all scheduled tasks
list :: Aff (Either String (Array ScheduledTask))
list = fromEffectFnAff listFFI

-- | FFI: Schedule task
foreign import scheduleFFI :: ScheduledTask -> EffectFnAff (Either String Unit)

-- | FFI: Cancel task
foreign import cancelFFI :: String -> EffectFnAff (Either String Unit)

-- | FFI: List tasks
foreign import listFFI :: EffectFnAff (Either String (Array ScheduledTask))
