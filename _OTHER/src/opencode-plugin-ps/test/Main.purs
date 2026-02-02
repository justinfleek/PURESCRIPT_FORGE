-- | OpenCode Plugin Test Suite
-- | PureScript test infrastructure
module Test.Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Test.Spec (describe)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Opencode.Plugin.MainSpec as MainSpec
import Test.Bridge.FFI.WebSocket.ClientSpec as WebSocketClientSpec
import Test.Bridge.FFI.OpenCode.PluginSpec as PluginSpec

-- | Test suite entry point
main :: Effect Unit
main = do
  log "OpenCode Plugin Test Suite"
  runSpec [consoleReporter] do
    describe "OpenCode Plugin Tests" do
      describe "Plugin Main" do
        MainSpec.testPluginHooks
        MainSpec.testEventHandling
        MainSpec.testProperties
      
      describe "WebSocket Client FFI" do
        WebSocketClientSpec.testConnection
        WebSocketClientSpec.testMessageHandling
        WebSocketClientSpec.testProperties
      
      describe "OpenCode Plugin FFI" do
        PluginSpec.testSDKIntegration
        PluginSpec.testProperties
