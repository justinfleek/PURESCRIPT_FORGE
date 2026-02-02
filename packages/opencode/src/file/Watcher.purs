-- | File watcher
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/file/watcher.ts
module Opencode.File.Watcher where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Watch event type
data WatchEventType = Created | Modified | Deleted

-- | Watch event
type WatchEvent =
  { type :: WatchEventType
  , path :: String
  }

-- | Watcher instance
type Watcher =
  { close :: Effect Unit
  }

-- | Watch a directory for changes
watch :: String -> (WatchEvent -> Effect Unit) -> Aff (Either String Watcher)
watch path handler = notImplemented "File.Watcher.watch"
