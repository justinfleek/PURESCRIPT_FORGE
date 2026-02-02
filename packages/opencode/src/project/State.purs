-- | Project State
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/project/state.ts
module Opencode.Project.State where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Project state
type ProjectState =
  { isInitialized :: Boolean
  , hasConfig :: Boolean
  , lastUpdated :: Number
  }

-- | Get project state
getState :: String -> Aff (Either String ProjectState)
getState projectId = notImplemented "Project.State.getState"

-- | Update project state
setState :: String -> ProjectState -> Aff (Either String Unit)
setState projectId state = notImplemented "Project.State.setState"
