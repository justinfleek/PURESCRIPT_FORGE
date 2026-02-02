-- | Configuration Tests
-- | Unit and property tests for configuration loading
module Test.Bridge.ConfigSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue)
import Effect (Effect)
import Effect.Class (liftEffect)
import Bridge.Config (loadConfig, Config)
import Bridge.Utils.Validation (validateRange, validateNonEmpty, validatePositive)

-- | Test default configuration
testDefaultConfig :: forall m. Monad m => m Unit
testDefaultConfig = do
  describe "Default Configuration" do
    it "loads default port" do
      config <- liftEffect loadConfig
      config.port `shouldEqual` 8765
    
    it "loads default host" do
      config <- liftEffect loadConfig
      config.host `shouldEqual` "127.0.0.1"
    
    it "loads default static directory" do
      config <- liftEffect loadConfig
      config.staticDir `shouldEqual` "./dist"

-- | Test configuration validation
testConfigValidation :: forall m. Monad m => m Unit
testConfigValidation = do
  describe "Configuration Validation" do
    it "validates port range" do
      config <- liftEffect loadConfig
      validateRange 1.0 65535.0 (fromInt config.port) `shouldBeTrue`
    
    it "validates host is non-empty" do
      config <- liftEffect loadConfig
      validateNonEmpty config.host `shouldBeTrue`
    
    it "validates sync interval is positive" do
      config <- liftEffect loadConfig
      validatePositive (fromInt config.storage.syncIntervalMinutes) `shouldBeTrue`

-- | Property: Configuration always has valid values
prop_configAlwaysValid :: Config -> Boolean
prop_configAlwaysValid config =
  validateRange 1.0 65535.0 (fromInt config.port) &&
  validateNonEmpty config.host &&
  validateNonEmpty config.staticDir &&
  validatePositive (fromInt config.storage.syncIntervalMinutes)

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "configuration always has valid values" do
      quickCheck prop_configAlwaysValid

foreign import fromInt :: Int -> Number
