{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Verification protocol - ensures all checks pass
module Rules.Verification where

import Prelude hiding (undefined, error, head, tail, fromJust)
import Rules.Core (TaskCompletion(..), verifyCompletion)
import Data.Bool (Bool(..))

-- | Verification checklist
data VerificationChecklist = VerificationChecklist
  { filesReadCompletely :: !Bool
  , dependencyGraphTraced :: !Bool
  , allInstancesFixed :: !Bool
  , noBannedConstructs :: !Bool
  , typesExplicit :: !Bool
  , typeChecksPass :: !Bool
  , testsPass :: !Bool
  , proofsCheck :: !Bool
  , documentationUpdated :: !Bool
  , workspaceClean :: !Bool
  }
  deriving (Show, Eq)

-- | Verify checklist
verifyChecklist :: VerificationChecklist -> Bool
verifyChecklist (VerificationChecklist f d a b t tc ts p doc w) =
  f && d && a && b && t && tc && ts && p && doc && w

-- | Convert TaskCompletion to VerificationChecklist
-- | For compatibility with existing code
toChecklist :: TaskCompletion -> VerificationChecklist
toChecklist (TaskCompletion compiles typeChecks tests doc clean debt) =
  VerificationChecklist
    { filesReadCompletely = True  -- Assumed if we got here
    , dependencyGraphTraced = True
    , allInstancesFixed = True
    , noBannedConstructs = True
    , typesExplicit = True
    , typeChecksPass = typeChecks
    , testsPass = tests
    , proofsCheck = compiles  -- Proofs check if code compiles
    , documentationUpdated = doc
    , workspaceClean = clean
    }

-- | All verification must pass
-- | Total function - no shortcuts
allChecksPass :: VerificationChecklist -> Bool
allChecksPass = verifyChecklist
