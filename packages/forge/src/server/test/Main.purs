-- | Bridge Server Test Suite
-- | PureScript test infrastructure
module Test.Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Test.Spec (describe)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Bridge.State.StoreSpec as StoreSpec
import Test.Bridge.Protocol.JsonRpcSpec as JsonRpcSpec
import Test.Bridge.E2E.WebSocketSpec as WebSocketE2E
import Test.Bridge.E2E.VeniceSpec as VeniceE2E
import Test.Bridge.E2E.OpencodeSpec as OpencodeE2E
import Test.Bridge.E2E.DatabaseSpec as DatabaseE2E
import Test.Bridge.Integration.FFISpec as FFIIntegration
import Test.Bridge.Integration.StateSyncSpec as StateSyncIntegration

-- | Test suite entry point
main :: Effect Unit
main = do
  log "Bridge Server Test Suite"
  runSpec [consoleReporter] do
    describe "Bridge Server Tests" do
      describe "State Store" do
        StoreSpec.testBalanceInvariants
        StoreSpec.testSessionInvariants
        StoreSpec.testStateTransitions
      
      describe "JSON-RPC Protocol" do
        JsonRpcSpec.testRequestValidity
        JsonRpcSpec.testResponseValidity
        JsonRpcSpec.testErrorValidity
      
      describe "E2E Tests" do
        describe "WebSocket" do
          WebSocketE2E.testWebSocketConnection
          WebSocketE2E.testJsonRpcFlow
          WebSocketE2E.testStateSync
          WebSocketE2E.testNotificationFlow
        
        describe "Venice API" do
          VeniceE2E.testChatCompletion
          VeniceE2E.testRateLimiting
          VeniceE2E.testModelListing
        
        describe "OpenCode Integration" do
          OpencodeE2E.testEventProcessing
          OpencodeE2E.testEventStream
        
        describe "Database" do
          DatabaseE2E.testDatabaseOperations
          DatabaseE2E.testDatabaseSync
      
      describe "Integration Tests" do
        describe "FFI Integration" do
          FFIIntegration.testDatabaseFFI
          FFIIntegration.testAnalyticsFFI
          FFIIntegration.testNodeFFI
        
        describe "State Synchronization" do
          StateSyncIntegration.testStateSyncFlow
          StateSyncIntegration.testNotificationSync
      
      describe "Utility Tests" do
        describe "JSON Utilities" do
          JsonSpec.testJsonParsing
          JsonSpec.testJsonStructureValidation
          JsonSpec.testFieldExtraction
          JsonSpec.testProperties
        
        describe "Validation Utilities" do
          ValidationSpec.testNonNegative
          ValidationSpec.testPositive
          ValidationSpec.testRange
          ValidationSpec.testNonEmpty
          ValidationSpec.testLength
          ValidationSpec.testSessionId
          ValidationSpec.testJsonRpcVersion
          ValidationSpec.testMethodName
          ValidationSpec.testTimestamp
          ValidationSpec.testProperties
        
        describe "Time Utilities" do
          TimeSpec.testTimeRemaining
          TimeSpec.testTimeFormatting
          TimeSpec.testPadZero
          TimeSpec.testProperties
        
        describe "Error Handling Utilities" do
          ErrorHandlingSpec.testSafeExecute
          ErrorHandlingSpec.testRetryWithBackoff
          ErrorHandlingSpec.testProperties
        
        describe "Metrics Utilities" do
          MetricsSpec.testAverageResponseTime
          MetricsSpec.testCost
          MetricsSpec.testConsumptionRate
          MetricsSpec.testTimeToDepletion
          MetricsSpec.testAggregateMetrics
          MetricsSpec.testProperties
      
      describe "Core Module Tests" do
        describe "Configuration" do
          ConfigSpec.testDefaultConfig
          ConfigSpec.testConfigValidation
          ConfigSpec.testProperties
        
        describe "Rate Limiter" do
          RateLimiterSpec.testRateLimiterCreation
          RateLimiterSpec.testAcquireRateLimit
          RateLimiterSpec.testUpdateFromResponse
          RateLimiterSpec.testProperties
        
        describe "WebSocket Manager" do
          ManagerSpec.testManagerCreation
          ManagerSpec.testBroadcast
          ManagerSpec.testProperties
        
        describe "Server" do
          ServerSpec.testServerInitialization
          ServerSpec.testServerStartup
          ServerSpec.testProperties
        
        describe "Main Entry Point" do
          MainSpec.testMainEntryPoint
        
        describe "Notification Service" do
          NotificationSpec.testNotificationServiceCreation
          NotificationSpec.testNotificationTypes
          NotificationSpec.testLowBalanceNotification
          NotificationSpec.testNotificationDismissal
          NotificationSpec.testProperties
      
      describe "FFI Module Tests" do
        describe "Node Database FFI" do
          DatabaseFFISpec.testDatabaseOperations
          DatabaseFFISpec.testUUIDGeneration
          DatabaseFFISpec.testProperties
        
        describe "Node Express FFI" do
          ExpressFFISpec.testExpressAppCreation
          ExpressFFISpec.testRouteHandlers
          ExpressFFISpec.testRequestResponse
          ExpressFFISpec.testProperties
        
        describe "Node Fetch FFI" do
          FetchFFISpec.testFetchRequests
          FetchFFISpec.testResponseOperations
          FetchFFISpec.testProperties
        
        describe "Node Pino FFI" do
          PinoFFISpec.testLoggerCreation
          PinoFFISpec.testLoggingFunctions
          PinoFFISpec.testFieldLogging
        
        describe "Node WebSocket FFI" do
          WebSocketFFISpec.testServerCreation
          WebSocketFFISpec.testConnectionHandling
          WebSocketFFISpec.testEventHandlers
          WebSocketFFISpec.testProperties
        
        describe "Node Handlers FFI" do
          HandlersFFISpec.testRequestDecoding
          HandlersFFISpec.testResponseEncoding
          HandlersFFISpec.testAuthentication
          HandlersFFISpec.testProperties
      
      describe "Performance Tests" do
        Benchmarks.benchmarkStateUpdate
        Benchmarks.benchmarkDatabaseOperations
        Benchmarks.benchmarkStateSync
        Benchmarks.benchmarkJsonRpcRequest
      
      describe "Stress Tests" do
        StressTests.testConcurrentConnections
        StressTests.testRapidStateUpdates
        StressTests.testLargePayloads
        StressTests.testMemoryPressure
        StressTests.testErrorRecovery

import Test.Bridge.Performance.Benchmarks as Benchmarks
import Test.Bridge.Stress.StressTests as StressTests
import Test.Bridge.Utils.JsonSpec as JsonSpec
import Test.Bridge.Utils.ValidationSpec as ValidationSpec
import Test.Bridge.Utils.TimeSpec as TimeSpec
import Test.Bridge.Utils.ErrorHandlingSpec as ErrorHandlingSpec
import Test.Bridge.Utils.MetricsSpec as MetricsSpec
import Test.Bridge.Venice.RateLimiterSpec as RateLimiterSpec
import Test.Bridge.WebSocket.ManagerSpec as ManagerSpec
import Test.Bridge.ConfigSpec as ConfigSpec
import Test.Bridge.ServerSpec as ServerSpec
import Test.Bridge.MainSpec as MainSpec
import Test.Bridge.Notifications.ServiceSpec as NotificationSpec
import Test.Bridge.FFI.Node.DatabaseSpec as DatabaseFFISpec
import Test.Bridge.FFI.Node.ExpressSpec as ExpressFFISpec
import Test.Bridge.FFI.Node.FetchSpec as FetchFFISpec
import Test.Bridge.FFI.Node.PinoSpec as PinoFFISpec
import Test.Bridge.FFI.Node.WebSocketSpec as WebSocketFFISpec
import Test.Bridge.FFI.Node.HandlersSpec as HandlersFFISpec
