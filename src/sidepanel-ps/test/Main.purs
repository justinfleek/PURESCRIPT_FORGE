-- | Test suite entry point
module Test.Main where

import Prelude
import Effect (Effect)
import Test.Spec (Spec, describe)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)

import Test.Sidepanel.State.ReducerSpec as ReducerSpec
import Test.Sidepanel.Utils.CurrencySpec as CurrencySpec
import Test.Sidepanel.Utils.TimeSpec as TimeSpec
import Test.Sidepanel.State.BalanceSpec as BalanceSpec
import Test.Sidepanel.RouterSpec as RouterSpec
import Test.Sidepanel.Api.BridgeSpec as BridgeSpec
import Test.Sidepanel.Theme.PrismSpec as PrismSpec
import Test.Sidepanel.WebSocket.ClientSpec as WebSocketClientSpec
import Test.Sidepanel.State.AppStateSpec as AppStateSpec
import Test.Sidepanel.FFI.WebSocketSpec as WebSocketFFISpec
import Test.Sidepanel.Property.UndoRedoProps as UndoRedoProps
import Test.Sidepanel.Property.ReducerProps as ReducerProps
import Test.Sidepanel.Property.TokenUsageProps as TokenUsageProps
import Test.Sidepanel.Utils.TokenUsageSpec as TokenUsageSpec

main :: Effect Unit
main = runSpec [consoleReporter] do
  describe "Sidepanel Tests" do
    ReducerSpec.spec
    CurrencySpec.spec
    TimeSpec.spec
    BalanceSpec.spec
    
    describe "Router" do
      RouterSpec.testRouteParsing
      RouterSpec.testRoutePrinting
      RouterSpec.testRouteToPanel
      RouterSpec.testProperties
    
    describe "Bridge API" do
      BridgeSpec.testJsonCodecs
      BridgeSpec.testProperties
    
    describe "PRISM Theme" do
      PrismSpec.testFleekColors
      PrismSpec.testHolographicTheme
      PrismSpec.testFleekTheme
      PrismSpec.testProperties
    
    describe "WebSocket Client" do
      WebSocketClientSpec.testClientCreation
      WebSocketClientSpec.testConnection
      WebSocketClientSpec.testRequestResponse
      WebSocketClientSpec.testSubscriptions
      WebSocketClientSpec.testProperties
    
    describe "App State" do
      AppStateSpec.testInitialState
      AppStateSpec.testProofState
      AppStateSpec.testUIState
      AppStateSpec.testProperties
    
    describe "WebSocket FFI" do
      WebSocketFFISpec.testWebSocketCreation
      WebSocketFFISpec.testReadyState
      WebSocketFFISpec.testMessageOperations
      WebSocketFFISpec.testConnectionOperations
      WebSocketFFISpec.testEventHandlers
      WebSocketFFISpec.testProperties
    
    describe "Property Tests" do
      UndoRedoProps.spec
      ReducerProps.spec
      TokenUsageProps.spec
    
    describe "Token Usage Utilities" do
      TokenUsageSpec.spec
      TokenUsageProps.spec
    
    describe "Token Usage Utilities" do
      TokenUsageSpec.spec