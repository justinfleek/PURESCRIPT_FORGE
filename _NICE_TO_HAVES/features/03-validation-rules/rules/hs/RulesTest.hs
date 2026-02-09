{-# LANGUAGE NoImplicitPrelude #-}

-- | Property tests for rules
module RulesTest where

import Prelude hiding (undefined, error, head, tail, fromJust)
import Rules.Core (TaskCompletion(..), verifyCompletion)
import Rules.TypeSafety (explicitDefault, explicitConditional)
import Rules.Verification (VerificationChecklist(..), verifyChecklist)
import Test.QuickCheck

-- | Property: Task completion requires all verifications
prop_taskCompletionRequiresAll :: TaskCompletion -> Property
prop_taskCompletionRequiresAll tc =
  verifyCompletion tc ==>
    codeCompiles tc &&
    typeChecks tc &&
    testsPass tc &&
    documentationUpdated tc &&
    workspaceClean tc &&
    noTechnicalDebt tc

-- | Property: explicitDefault preserves type safety
prop_explicitDefaultTypeSafe :: Maybe Int -> Int -> Property
prop_explicitDefaultTypeSafe opt default =
  let result = explicitDefault opt default
  in case opt of
    Nothing -> result === default
    Just value -> result === value

-- | Property: explicitConditional is deterministic
prop_explicitConditionalDeterministic :: Bool -> Int -> Int -> Property
prop_explicitConditionalDeterministic cond value default =
  let result = explicitConditional cond value default
  in if cond
     then result === value
     else result === default

-- | Property: Verification checklist requires all checks
prop_verificationRequiresAll :: VerificationChecklist -> Property
prop_verificationRequiresAll vc =
  verifyChecklist vc ==>
    filesReadCompletely vc &&
    dependencyGraphTraced vc &&
    allInstancesFixed vc &&
    noBannedConstructs vc &&
    typesExplicit vc &&
    typeChecksPass vc &&
    testsPass vc &&
    proofsCheck vc &&
    documentationUpdated vc &&
    workspaceClean vc

-- | Run all tests
main :: IO ()
main = do
  putStrLn "Running property tests..."
  quickCheck prop_taskCompletionRequiresAll
  quickCheck prop_explicitDefaultTypeSafe
  quickCheck prop_explicitConditionalDeterministic
  quickCheck prop_verificationRequiresAll
  putStrLn "All tests passed!"
