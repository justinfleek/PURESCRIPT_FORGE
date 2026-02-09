-- | Debug Snapshot command
module Forge.CLI.Cmd.Debug.Snapshot where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

foreign import debugSnapshotFFI :: Aff (Either String Unit)

-- | Execute debug snapshot command
execute :: Aff (Either String Unit)
execute = debugSnapshotFFI
