-- | Git Worktree management
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/worktree/index.ts
module Opencode.Worktree.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

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
