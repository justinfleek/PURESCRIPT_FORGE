-- | Integration between Test.Spec and Test.QuickCheck
-- | Provides helpers to run QuickCheck properties inside Spec test blocks.
-- | This is a local stub for the spec-quickcheck package.
module Test.Spec.QuickCheck
  ( quickCheck
  , module ReExport
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Test.QuickCheck as QC
import Test.QuickCheck (class Testable)
import Test.QuickCheck (withHelp, (<?>) ) as ReExport

-- | Run a QuickCheck property inside an Aff context (for use with Test.Spec `it` blocks).
-- | Runs 100 test cases. Throws an exception if the property fails.
quickCheck :: forall prop. Testable prop => prop -> Aff Unit
quickCheck prop = liftEffect (QC.quickCheck prop)
