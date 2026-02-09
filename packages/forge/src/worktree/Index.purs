-- | Git Worktree management
-- | 1:1 parity with opencode-dev/packages/opencode/src/worktree/index.ts
module Forge.Worktree.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

type Worktree =
  { path :: String
  , branch :: String
  , isMain :: Boolean
  }

foreign import listWorktrees :: Aff (Either String (Array Worktree))
foreign import createWorktree :: String -> String -> Aff (Either String Worktree)
foreign import removeWorktree :: String -> Aff (Either String Unit)

list :: Aff (Either String (Array Worktree))
list = listWorktrees

create :: String -> String -> Aff (Either String Worktree)
create path branch = createWorktree path branch

remove :: String -> Aff (Either String Unit)
remove path = removeWorktree path
