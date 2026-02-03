-- | Project State
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/project/state.ts
module Forge.Project.State where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

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
