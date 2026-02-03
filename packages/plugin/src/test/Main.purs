-- | Forge Plugin Test Suite
-- | PureScript test infrastructure
module Test.Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Test.Spec (describe)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Forge.Plugin.MainSpec as MainSpec
import Test.Bridge.FFI.WebSocket.ClientSpec as WebSocketClientSpec
import Test.Bridge.FFI.Forge.PluginSpec as PluginSpec

-- | Test suite entry point
main :: Effect Unit
main = do
  log "Forge Plugin Test Suite"
  runSpec [consoleReporter] do
    describe "Forge Plugin Tests" do
      describe "Plugin Main" do
        MainSpec.testPluginHooks
        MainSpec.testEventHandling
        MainSpec.testProperties
      
      describe "WebSocket Client FFI" do
        WebSocketClientSpec.testConnection
        WebSocketClientSpec.testMessageHandling
        WebSocketClientSpec.testProperties
      
      describe "Forge Plugin FFI" do
        PluginSpec.testSDKIntegration
        PluginSpec.testProperties
