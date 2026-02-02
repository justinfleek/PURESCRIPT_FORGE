-- | OpenCode Plugin Test Suite
module Test.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Opencode.Plugin.MainSpec as MainSpec
import Test.Bridge.FFI.WebSocket.ClientSpec as WebSocketClientSpec
import Test.Bridge.FFI.OpenCode.PluginSpec as PluginSpec

-- | Test suite entry point
main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  MainSpec.spec
  WebSocketClientSpec.spec
  PluginSpec.spec
