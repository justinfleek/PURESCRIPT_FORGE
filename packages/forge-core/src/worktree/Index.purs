-- | Git Worktree management
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/worktree/index.ts
module Forge.Worktree.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Worktree info
type Worktree =
  { path :: String
  , branch :: String
  , isMain :: Boolean
  }

-- | List worktrees
list :: Aff (Either String (Array Worktree))
list = notImplemented "Worktree.Index.list"

-- | Create a worktree
create :: String -> String -> Aff (Either String Worktree)
create path branch = notImplemented "Worktree.Index.create"

-- | Remove a worktree
remove :: String -> Aff (Either String Unit)
remove path = notImplemented "Worktree.Index.remove"
