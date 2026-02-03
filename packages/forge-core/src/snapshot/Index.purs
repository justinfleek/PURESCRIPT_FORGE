-- | Snapshot management
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/snapshot/index.ts
module Forge.Snapshot.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Snapshot info
type Snapshot =
  { id :: String
  , sessionId :: String
  , messageId :: String
  , createdAt :: Number
  }

-- | Create a snapshot
create :: String -> String -> Aff (Either String Snapshot)
create sessionId messageId = notImplemented "Snapshot.Index.create"

-- | Restore from snapshot
restore :: String -> Aff (Either String Unit)
restore snapshotId = notImplemented "Snapshot.Index.restore"

-- | List snapshots for a session
list :: String -> Aff (Either String (Array Snapshot))
list sessionId = notImplemented "Snapshot.Index.list"
