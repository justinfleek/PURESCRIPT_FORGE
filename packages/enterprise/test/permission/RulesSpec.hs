{-# LANGUAGE NoImplicitPrelude #-}

-- | Property tests for rules
module Permission.RulesSpec where

import Prelude hiding (undefined, error, head, tail, fromJust)
import Permission.Rules.Core (TaskCompletion(..), verifyCompletion)
import Permission.Rules.TypeSafety (explicitDefault, explicitConditional)
import Permission.Rules.Verification (VerificationChecklist(..), verifyChecklist)
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
prop_explicitDefaultTypeSafe opt def =
  let result = explicitDefault opt def
  in case opt of
    Nothing -> result === def
    Just value -> result === value

-- | Property: explicitConditional is deterministic
prop_explicitConditionalDeterministic :: Bool -> Int -> Int -> Property
prop_explicitConditionalDeterministic cond value def =
  let result = explicitConditional cond value def
  in if cond
     then result === value
     else result === def

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
    vcTestsPass vc &&
    proofsCheck vc &&
    vcDocumentationUpdated vc &&
    vcWorkspaceClean vc

-- | Run all tests
main :: IO ()
main = do
  putStrLn "Running property tests..."
  quickCheck prop_taskCompletionRequiresAll
  quickCheck prop_explicitDefaultTypeSafe
  quickCheck prop_explicitConditionalDeterministic
  quickCheck prop_verificationRequiresAll
  putStrLn "All tests passed!"
