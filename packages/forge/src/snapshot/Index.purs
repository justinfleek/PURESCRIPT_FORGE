-- | Snapshot management
-- | 1:1 parity with opencode-dev/packages/opencode/src/snapshot/index.ts
module Forge.Snapshot.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

type Snapshot =
  { id :: String
  , sessionId :: String
  , messageId :: String
  , createdAt :: Number
  }

foreign import createImpl :: String -> String -> Aff (Either String Snapshot)
foreign import restoreImpl :: String -> Aff (Either String Unit)
foreign import listImpl :: String -> Aff (Either String (Array Snapshot))

create :: String -> String -> Aff (Either String Snapshot)
create sessionId messageId = createImpl sessionId messageId

restore :: String -> Aff (Either String Unit)
restore snapshotId = restoreImpl snapshotId

list :: String -> Aff (Either String (Array Snapshot))
list sessionId = listImpl sessionId
