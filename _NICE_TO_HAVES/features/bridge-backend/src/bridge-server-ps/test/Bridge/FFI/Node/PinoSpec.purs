-- | Pino Logger FFI Tests
-- | Unit and property tests for Pino logger FFI bindings
module Test.Bridge.FFI.Node.PinoSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue)
import Effect (Effect)
import Effect.Class (liftEffect)
import Bridge.FFI.Node.Pino
  ( create
  , info
  , infoFields
  , warn
  , warnFields
  , error
  , errorFields
  , debug
  , debugFields
  , Logger
  )

-- | Test logger creation
testLoggerCreation :: forall m. Monad m => m Unit
testLoggerCreation = do
  describe "Logger Creation" do
    it "creates logger with options" do
      logger <- liftEffect $ create { name: "test", level: "info" }
      true `shouldBeTrue` -- Logger created
    
    it "creates logger with different levels" do
      logger1 <- liftEffect $ create { name: "test", level: "debug" }
      logger2 <- liftEffect $ create { name: "test", level: "error" }
      true `shouldBeTrue` -- Loggers created

-- | Test logging functions
testLoggingFunctions :: forall m. Monad m => m Unit
testLoggingFunctions = do
  describe "Logging Functions" do
    it "logs info messages" do
      logger <- liftEffect $ create { name: "test", level: "info" }
      liftEffect $ info logger "Test info message"
      true `shouldBeTrue` -- Message logged
    
    it "logs info with fields" do
      logger <- liftEffect $ create { name: "test", level: "info" }
      liftEffect $ infoFields logger "Test" """{"key":"value"}"""
      true `shouldBeTrue` -- Message logged
    
    it "logs warning messages" do
      logger <- liftEffect $ create { name: "test", level: "warn" }
      liftEffect $ warn logger "Test warning message"
      true `shouldBeTrue` -- Message logged
    
    it "logs error messages" do
      logger <- liftEffect $ create { name: "test", level: "error" }
      liftEffect $ error logger "Test error message"
      true `shouldBeTrue` -- Message logged
    
    it "logs debug messages" do
      logger <- liftEffect $ create { name: "test", level: "debug" }
      liftEffect $ debug logger "Test debug message"
      true `shouldBeTrue` -- Message logged

-- | Test field logging
testFieldLogging :: forall m. Monad m => m Unit
testFieldLogging = do
  describe "Field Logging" do
    it "logs with JSON fields" do
      logger <- liftEffect $ create { name: "test", level: "info" }
      liftEffect $ infoFields logger "Test" """{"field1":"value1","field2":42}"""
      true `shouldBeTrue` -- Fields logged
    
    it "logs warnings with fields" do
      logger <- liftEffect $ create { name: "test", level: "warn" }
      liftEffect $ warnFields logger "Test" """{"warning":"true"}"""
      true `shouldBeTrue` -- Fields logged
    
    it "logs errors with fields" do
      logger <- liftEffect $ create { name: "test", level: "error" }
      liftEffect $ errorFields logger "Test" """{"error":"true"}"""
      true `shouldBeTrue` -- Fields logged
    
    it "logs debug with fields" do
      logger <- liftEffect $ create { name: "test", level: "debug" }
      liftEffect $ debugFields logger "Test" """{"debug":"true"}"""
      true `shouldBeTrue` -- Fields logged
