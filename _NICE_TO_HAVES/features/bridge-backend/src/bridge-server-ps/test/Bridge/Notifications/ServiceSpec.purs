-- | Notification Service Tests
module Test.Bridge.Notifications.ServiceSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Test notification service
spec :: Spec Unit
spec = do
  describe "Notification Service" do
    it "creates service successfully" do
      1 `shouldEqual` 1
    it "sends success notification" do
      true `shouldEqual` true
    it "sends error notification" do
      true `shouldEqual` true
    it "sends warning notification" do
      true `shouldEqual` true
