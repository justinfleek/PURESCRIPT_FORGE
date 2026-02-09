-- | Test Suite Entry Point
-- | Runs all analytics tests
module Main where

import Test.Hspec
import qualified Bridge.AnalyticsSpec as AnalyticsSpec
import qualified Bridge.AnalyticsE2ESpec as AnalyticsE2E
import qualified Bridge.AnalyticsQueriesSpec as AnalyticsQueriesSpec
import qualified Bridge.AnalyticsDuckDBSpec as AnalyticsDuckDBSpec

main :: IO ()
main = hspec $ do
  AnalyticsSpec.spec
  AnalyticsSpec.testInvariants
  AnalyticsE2E.spec
  AnalyticsE2E.testPerformance
  AnalyticsQueriesSpec.spec
  AnalyticsDuckDBSpec.spec
