-- | Git Worktree management
module Opencode.Worktree.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

-- | Worktree info
type Worktree =
  { path :: String
  , branch :: String
  , isMain :: Boolean
  }

-- | List worktrees
list :: Aff (Either String (Array Worktree))
list = listWorktrees

-- | Create a worktree
create :: String -> String -> Aff (Either String Worktree)
create path branch = createWorktree path branch

-- | Remove a worktree
remove :: String -> Aff (Either String Unit)
remove path = removeWorktree path

foreign import listWorktrees :: Aff (Either String (Array Worktree))
foreign import createWorktree :: String -> String -> Aff (Either String Worktree)
foreign import removeWorktree :: String -> Aff (Either String Unit)
