-- | Project VCS (Version Control System)
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/project/vcs.ts
module Forge.Project.VCS where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | VCS type
data VCSType = Git | Mercurial | SVN | None

-- | VCS info
type VCSInfo =
  { type :: VCSType
  , root :: String
  , branch :: Maybe String
  , isClean :: Boolean
  }

-- | Detect VCS in directory
detect :: String -> Aff (Either String VCSInfo)
detect directory = notImplemented "Project.VCS.detect"

-- | Get current branch
getCurrentBranch :: String -> Aff (Maybe String)
getCurrentBranch directory = notImplemented "Project.VCS.getCurrentBranch"

-- | Check if working directory is clean
isClean :: String -> Aff Boolean
isClean directory = notImplemented "Project.VCS.isClean"
