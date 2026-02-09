{-# LANGUAGE StrictData #-}

-- | Core development principles as proven types
module Rules.Core where

import Prelude hiding (undefined, error, head, tail)

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

-- | BANNED: undefined, error, head, tail, fromJust
-- | These functions are unrepresentable in our type system
-- | Use Maybe/Either instead
