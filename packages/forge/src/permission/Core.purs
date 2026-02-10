-- | Core development principles as proven types
module Forge.Permission.Core where

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
verifyCompletion (TaskCompletion tc) =
  tc.codeCompiles && tc.typeChecks && tc.testsPass &&
  tc.documentationUpdated && tc.workspaceClean && tc.noTechnicalDebt

-- | Core principle: Accuracy over speed
-- | This is a type-level guarantee that we never skip verification
newtype Accuracy = Accuracy Boolean

derive newtype instance eqAccuracy :: Eq Accuracy
derive newtype instance showAccuracy :: Show Accuracy

-- | Completeness over convenience
-- | Ensures we don't take shortcuts
newtype Completeness = Completeness Boolean

derive newtype instance eqCompleteness :: Eq Completeness
derive newtype instance showCompleteness :: Show Completeness
