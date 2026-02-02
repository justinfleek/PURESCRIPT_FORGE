module Nexus.AgentOrchestrator.FFI where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Data.Either (Either(..))

-- | Call bubblewrap with arguments
-- | Returns process ID on success
foreign import callBubblewrap :: Array String -> Aff (Either String Int)

-- | Generate deterministic agent ID from namespace and seed
-- | Same namespace + seed always produces same ID
foreign import generateAgentIdFromSeed :: String -> Int -> String

-- | Format timestamp (milliseconds since epoch) as ISO 8601 string
-- | Deterministic: same input always produces same output
foreign import formatTimestamp :: Number -> String

-- | Kill process by PID
foreign import killProcess :: Int -> Effect (Either String Unit)
