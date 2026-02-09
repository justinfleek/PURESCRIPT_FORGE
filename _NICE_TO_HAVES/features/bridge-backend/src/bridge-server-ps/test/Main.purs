-- | Bridge Server Test Suite
module Test.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec (describe, it, Spec)
import Test.Spec.Assertions (shouldEqual)
import Test.Bridge.Notifications.ServiceSpec as NotificationSpec

-- | Test suite entry point
main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  describe "Bridge Server Tests" do
    NotificationSpec.spec
    basicTests

-- | Basic placeholder tests
basicTests :: Spec Unit
basicTests = do
  describe "Basic Tests" do
    it "placeholder test" do
      1 `shouldEqual` 1
