-- | Project module
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/project/project.ts
module Opencode.Project.Project where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Project info
type ProjectInfo =
  { root :: String
  , name :: String
  , type :: Maybe String
  , gitRoot :: Maybe String
  }

-- | Get project info
get :: String -> Aff (Either String ProjectInfo)
get directory = notImplemented "Project.Project.get"

-- | Detect project type
detectType :: String -> Aff (Maybe String)
detectType directory = notImplemented "Project.Project.detectType"
