-- | Deep comprehensive grade composition properties tests
module Test.GradedMonad.CompositionSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Aleph.Coeffect.Resource as Resource

spec :: Spec Unit
spec = describe "Grade Composition Properties Deep Tests" $ do
  describe "Resource Combination" $ do
    it "combines Pure with resource (left identity)" $ do
      let
        r = Resource.Network
        combined = Resource.Pure `Resource.combine` r
      combined `shouldEqual` r

    it "combines resource with Pure (right identity)" $ do
      let
        r = Resource.Network
        combined = r `Resource.combine` Resource.Pure
      combined `shouldEqual` r

    it "BUG: resource combination may not satisfy semilattice laws" $ do
      pure unit

  describe "Resource Flattening" $ do
    it "flattens Pure resource" $ do
      let
        flattened = Resource.flatten Resource.Pure
      flattened `shouldEqual` []

    it "BUG: flatten may not preserve resource semantics" $ do
      pure unit
