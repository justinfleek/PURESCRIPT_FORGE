-- | Forge Test Suite Entry Point
module Main where

import Test.Hspec
import qualified RulesSpec
import qualified ValidatorSpec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Forge Core" $ do
    RulesSpec.spec
    ValidatorSpec.spec
