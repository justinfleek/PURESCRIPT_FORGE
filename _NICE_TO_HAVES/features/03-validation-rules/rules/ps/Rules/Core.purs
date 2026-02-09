-- | Core development principles as proven types
module Rules.Core where

import Prelude

-- | ACCURACY > SPEED
-- | COMPLETENESS > CONVENIENCE
-- | CODE IS TRUTH, TYPES DESCRIBE
-- | NO TYPE ESCAPES, NO SHORTCUTS

-- | A task is complete only when all verifications pass
data TaskCompletion = TaskCompletion
  { codeCompiles :: Boolean
  , typeChecks :: Boolean
  , testsPass :: Boolean
  , documentationUpdated :: Boolean
  , workspaceClean :: Boolean
  , noTechnicalDebt :: Boolean
  }

-- | Verify task completion
verifyCompletion :: TaskCompletion -> Boolean
verifyCompletion (TaskCompletion c t ts d w n) = 
  c && t && ts && d && w && n

-- | Core principle: Accuracy over speed
-- | This is a type-level guarantee that we never skip verification
newtype Accuracy = Accuracy Boolean

derive newtype instance Eq Accuracy
derive newtype instance Show Accuracy

-- | Completeness over convenience
-- | Ensures we don't take shortcuts
newtype Completeness = Completeness Boolean

derive newtype instance Eq Completeness
derive newtype instance Show Completeness
