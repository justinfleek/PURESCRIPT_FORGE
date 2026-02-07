-- | Bridge Main Tests
-- | Unit tests for main entry point
module Test.Bridge.MainSpec where

import Prelude
import Test.Spec (describe, it, pending)
import Test.Spec.Assertions (shouldEqual)
import Effect.Class (liftEffect)
import Forge.Config (loadConfig)

-- | Test main entry point
testMainEntryPoint :: forall m. Monad m => m Unit
testMainEntryPoint = do
  describe "Main Entry Point" do
    it "loads configuration" do
      config <- liftEffect loadConfig
      config.port `shouldEqual` 8765

    pending "initializes server components (requires mock HttpServer)"
    pending "handles startup errors gracefully (requires mock HttpServer)"
