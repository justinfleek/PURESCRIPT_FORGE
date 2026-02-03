-- | Session Compaction - compress old messages
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/session/compaction.ts
module Forge.Session.Compaction where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Compaction configuration
type CompactionConfig =
  { maxMessages :: Int
  , summaryModel :: Maybe String
  , preserveSystemMessages :: Boolean
  }

-- | Compacted message summary
type CompactionResult =
  { originalCount :: Int
  , compactedCount :: Int
  , summary :: String
  }

-- | Compact session messages
compact :: String -> CompactionConfig -> Aff (Either String CompactionResult)
compact sessionId config = notImplemented "Session.Compaction.compact"

-- | Check if compaction is needed
needsCompaction :: String -> Int -> Aff Boolean
needsCompaction sessionId threshold = notImplemented "Session.Compaction.needsCompaction"
