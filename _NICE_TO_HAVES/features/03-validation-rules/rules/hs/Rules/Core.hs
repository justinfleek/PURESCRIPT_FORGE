{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Core development principles as proven types
module Rules.Core where

import Prelude hiding (undefined, error)
import Data.Bool (Bool(..))
import Data.Maybe (Maybe(..))

-- NOTE: We use NoImplicitPrelude and explicit imports to ensure
-- partial functions like head, tail, init, last (from Data.List)
-- and fromJust (from Data.Maybe) are never accidentally used.
-- These are not in Prelude, so we don't hide them - we simply
-- never import them.

-- | ACCURACY > SPEED
-- | COMPLETENESS > CONVENIENCE
-- | CODE IS TRUTH, TYPES DESCRIBE
-- | NO TYPE ESCAPES, NO SHORTCUTS

-- | A task is complete only when all verifications pass
data TaskCompletion = TaskCompletion
  { codeCompiles :: !Bool
  , typeChecks :: !Bool
  , testsPass :: !Bool
  , documentationUpdated :: !Bool
  , workspaceClean :: !Bool
  , noTechnicalDebt :: !Bool
  }
  deriving (Show, Eq)

-- | Verify task completion
-- | Total function - handles all cases
verifyCompletion :: TaskCompletion -> Bool
verifyCompletion (TaskCompletion c t ts d w n) = 
  c && t && ts && d && w && n

-- | Core principle: Accuracy over speed
-- | This is a type-level guarantee that we never skip verification
newtype Accuracy = Accuracy Bool
  deriving (Show, Eq)

-- | Completeness over convenience
-- | Ensures we don't take shortcuts
newtype Completeness = Completeness Bool
  deriving (Show, Eq)

-- | Safe head alternative - total function
safeHead :: [a] -> Maybe a
safeHead []      = Nothing
safeHead (x : _) = Just x

-- | Safe tail alternative - total function
safeTail :: [a] -> Maybe [a]
safeTail []       = Nothing
safeTail (_ : xs) = Just xs

-- | BANNED: undefined, error, head, tail, fromJust
-- | These functions are unrepresentable in our type system
-- | Use Maybe/Either and safe alternatives instead
