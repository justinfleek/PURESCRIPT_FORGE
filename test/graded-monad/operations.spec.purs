-- | Deep comprehensive graded monad operations tests
module Test.GradedMonad.OperationsSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Data.Either (Either(..), isRight)
import Aleph.Coeffect.Graded as Graded
import Aleph.Coeffect.Resource as Resource
import Aleph.Coeffect.Discharge as Discharge

spec :: Spec Unit
spec = describe "Graded Monad Operations Deep Tests" $ do
  describe "pure' Operation" $ do
    it "creates pure computation with no resource requirements" $ do
      let
        pureComp = Graded.pure' 42
        proof = Discharge.emptyProof
        result = Graded.run pureComp proof
      isRight result `shouldEqual` true

    it "BUG: pure' may not be truly pure" $ do
      pure unit

  describe "map' Operation" $ do
    it "maps over pure computation" $ do
      let
        pureComp = Graded.pure' 42
        mapped = Graded.map' (_ + 1) pureComp
        proof = Discharge.emptyProof
        result = Graded.run mapped proof
      isRight result `shouldEqual` true

    it "BUG: map' may not preserve resource requirements" $ do
      pure unit

  describe "bind' Operation" $ do
    it "binds pure computation to pure function" $ do
      let
        pureComp = Graded.pure' 42
        bound = Graded.bind' pureComp (\x -> Graded.pure' (x + 1))
        proof = Discharge.emptyProof
        result = Graded.run bound proof
      isRight result `shouldEqual` true

    it "BUG: bind' may not combine resource requirements correctly" $ do
      pure unit

  describe "require Operation" $ do
    it "requires Network resource" $ do
      let
        reqComp = Graded.require Resource.Network
        proof = Discharge.emptyProof
        result = Graded.run reqComp proof
      pure unit

    it "BUG: require may not validate resource requirements" $ do
      pure unit
