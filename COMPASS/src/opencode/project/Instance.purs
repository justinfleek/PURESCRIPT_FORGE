-- | Project Instance
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/project/instance.ts
module Opencode.Project.Instance where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Instance configuration
type InstanceConfig a =
  { directory :: String
  , init :: Unit
  , fn :: Aff a
  }

-- | Provide an instance
provide :: forall a. InstanceConfig a -> Aff (Either String a)
provide config = notImplemented "Project.Instance.provide"

-- | Dispose the current instance
dispose :: Aff (Either String Unit)
dispose = notImplemented "Project.Instance.dispose"
