-- | Test Main - Entry point for all tests
-- | Runs all unit, property, and integration tests
module Test.Main where

import Prelude

import Effect (Effect)
import Test.Spec (describe)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)

-- Unit Tests
import Test.Unit.Util.AuthSpec as AuthSpec
import Test.Unit.Util.CostSpec as CostSpec
import Test.Unit.Util.DataDumperSpec as DataDumperSpec
import Test.Unit.Util.ErrorSpec as ErrorSpec
import Test.Unit.Util.Formatter.CurrencySpec as CurrencySpec
import Test.Unit.Util.Formatter.NumberSpec as NumberSpec
import Test.Unit.Util.Formatter.TimeSpec as TimeSpec
import Test.Unit.Util.HandlerHelpersSpec as HandlerHelpersSpec
import Test.Unit.Util.HandlerProviderSpec as HandlerProviderSpec
import Test.Unit.Util.LoggerSpec as LoggerSpec
import Test.Unit.Util.MessageEncryptionHelpersSpec as MessageEncryptionHelpersSpec
import Test.Unit.Util.MessageEncryptionSpec as MessageEncryptionSpec
import Test.Unit.Util.OpenAIHelperSpec as OpenAIHelperSpec
import Test.Unit.Util.Provider.AnthropicChunkSpec as AnthropicChunkSpec
import Test.Unit.Util.Provider.AnthropicRequestSpec as AnthropicRequestSpec
import Test.Unit.Util.Provider.AnthropicResponseSpec as AnthropicResponseSpec
import Test.Unit.Util.Provider.FormatConverterSpec as FormatConverterSpec
import Test.Unit.Util.Provider.GoogleChunkSpec as GoogleChunkSpec
import Test.Unit.Util.Provider.GoogleRequestSpec as GoogleRequestSpec
import Test.Unit.Util.Provider.GoogleResponseSpec as GoogleResponseSpec
import Test.Unit.Util.Provider.OpenAIChunkSpec as OpenAIChunkSpec
import Test.Unit.Util.Provider.OpenAICompatibleChunkSpec as OpenAICompatibleChunkSpec
import Test.Unit.Util.Provider.OpenAICompatibleRequestSpec as OpenAICompatibleRequestSpec
import Test.Unit.Util.Provider.OpenAICompatibleResponseSpec as OpenAICompatibleResponseSpec
import Test.Unit.Util.Provider.OpenAIRequestSpec as OpenAIRequestSpec
import Test.Unit.Util.Provider.OpenAIResponseSpec as OpenAIResponseSpec
import Test.Unit.Util.Provider.OpenAIUsageSpec as OpenAIUsageSpec
import Test.Unit.Util.ProviderHelpersSpec as ProviderHelpersSpec
import Test.Unit.Util.ProviderSpec as ProviderSpec
import Test.Unit.Util.RateLimiterSpec as RateLimiterSpec
import Test.Unit.Util.ReloadSpec as ReloadSpec
import Test.Unit.Util.StickyProviderTrackerSpec as StickyProviderTrackerSpec
import Test.Unit.Util.TrialLimiterSpec as TrialLimiterSpec
import Test.Unit.Util.ValidationSpec as ValidationSpec

-- Property Tests
import Test.Property.FormatterProps as FormatterProps
import Test.Property.MessageEncryptionProps as MessageEncryptionProps
import Test.Property.ProviderProps as ProviderProps
import Test.Property.ReducerProps as ReducerProps

-- Integration Tests
import Test.Integration.ErrorHandlingIntegrationSpec as ErrorHandlingIntegrationSpec
import Test.Integration.HandlerMainIntegrationSpec as HandlerMainIntegrationSpec

main :: Effect Unit
main = runSpec [consoleReporter] do
  describe "Console App Tests" do
    describe "Unit Tests" do
      describe "Util" do
        AuthSpec.spec
        CostSpec.spec
        DataDumperSpec.spec
        ErrorSpec.spec
        HandlerHelpersSpec.spec
        HandlerProviderSpec.spec
        LoggerSpec.spec
        MessageEncryptionHelpersSpec.spec
        MessageEncryptionSpec.spec
        OpenAIHelperSpec.spec
        ProviderHelpersSpec.spec
        ProviderSpec.spec
        RateLimiterSpec.spec
        ReloadSpec.spec
        StickyProviderTrackerSpec.spec
        TrialLimiterSpec.spec
        ValidationSpec.spec
      describe "Formatter" do
        CurrencySpec.spec
        NumberSpec.spec
        TimeSpec.spec
      describe "Provider" do
        AnthropicChunkSpec.spec
        AnthropicRequestSpec.spec
        AnthropicResponseSpec.spec
        FormatConverterSpec.spec
        GoogleChunkSpec.spec
        GoogleRequestSpec.spec
        GoogleResponseSpec.spec
        OpenAIChunkSpec.spec
        OpenAICompatibleChunkSpec.spec
        OpenAICompatibleRequestSpec.spec
        OpenAICompatibleResponseSpec.spec
        OpenAIRequestSpec.spec
        OpenAIResponseSpec.spec
        OpenAIUsageSpec.spec
    describe "Property Tests" do
      FormatterProps.spec
      MessageEncryptionProps.spec
      ProviderProps.spec
      ReducerProps.spec
    describe "Integration Tests" do
      ErrorHandlingIntegrationSpec.spec
      HandlerMainIntegrationSpec.spec
