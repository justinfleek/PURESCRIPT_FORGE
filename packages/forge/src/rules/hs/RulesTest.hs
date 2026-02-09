-- | Property tests for rules
module Main where

import Prelude hiding (undefined, error, head, tail)
import qualified Rules.Core as Core
import Rules.TypeSafety (explicitDefault, explicitConditional)
import qualified Rules.Verification as V
import Test.QuickCheck

-- | Arbitrary instance for TaskCompletion
instance Arbitrary Core.TaskCompletion where
  arbitrary = Core.TaskCompletion
    <$> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary

-- | Arbitrary instance for VerificationChecklist
instance Arbitrary V.VerificationChecklist where
  arbitrary = V.VerificationChecklist
    <$> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary
    <*> arbitrary

-- | Property: Task completion requires all verifications
prop_taskCompletionRequiresAll :: Core.TaskCompletion -> Property
prop_taskCompletionRequiresAll tc =
  Core.verifyCompletion tc ==>
    Core.codeCompiles tc &&
    Core.typeChecks tc &&
    Core.testsPass tc &&
    Core.documentationUpdated tc &&
    Core.workspaceClean tc &&
    Core.noTechnicalDebt tc

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
prop_verificationRequiresAll :: V.VerificationChecklist -> Property
prop_verificationRequiresAll vc =
  V.verifyChecklist vc ==>
    V.filesReadCompletely vc &&
    V.dependencyGraphTraced vc &&
    V.allInstancesFixed vc &&
    V.noBannedConstructs vc &&
    V.typesExplicit vc &&
    V.typeChecksPass vc &&
    V.testsPass vc &&
    V.proofsCheck vc &&
    V.documentationUpdated vc &&
    V.workspaceClean vc

-- | Run all tests
main :: IO ()
main = do
  putStrLn "Running property tests..."
  quickCheck prop_taskCompletionRequiresAll
  quickCheck prop_explicitDefaultTypeSafe
  quickCheck prop_explicitConditionalDeterministic
  quickCheck prop_verificationRequiresAll
  putStrLn "All tests passed!"
