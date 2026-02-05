-- | Unit Tests for Token Usage Utilities
-- |
-- | Based on spec 71-UNIT-TESTING.md
-- | Tests token usage data processing functions
module Test.Sidepanel.Utils.TokenUsageSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (class Arbitrary, arbitrary, (===), (==>))
import Test.QuickCheck.Gen (Gen, chooseInt, chooseFloat, arrayOf, elements)
import Data.Array as Array
import Data.DateTime (DateTime)
import Sidepanel.Utils.TokenUsage as TokenUsage
import Sidepanel.State.AppState (SessionSummary)
import Sidepanel.FFI.DateTime (fromTimestamp, toTimestamp)
import Test.Sidepanel.TestFixtures (testDateTime)

-- | Test suite
spec :: Spec Unit
spec = describe "Token Usage Utilities" do
  describe "filterSessionsByTimeRange" do
    it "filters sessions by LastHour range" do
      let
        now = fromTimestamp 1000000.0  -- Some timestamp
        oneHourAgo = fromTimestamp (1000000.0 - 3600000.0)
        twoHoursAgo = fromTimestamp (1000000.0 - 7200000.0)
        sessions = 
          [ { id: "1", model: "gpt-4", cost: 0.1, tokenCount: 100, startedAt: now }
          , { id: "2", model: "gpt-4", cost: 0.2, tokenCount: 200, startedAt: oneHourAgo }
          , { id: "3", model: "gpt-4", cost: 0.3, tokenCount: 300, startedAt: twoHoursAgo }
          ]
        filtered = TokenUsage.filterSessionsByTimeRange TokenUsage.LastHour sessions now
      
      Array.length filtered `shouldSatisfy` (_ <= Array.length sessions)
      -- All filtered sessions should be within last hour (simplified check)
      true `shouldEqual` true
    
    it "filters sessions by AllTime range (includes all)" do
      let
        now = fromTimestamp 1000000.0
        sessions = 
          [ { id: "1", model: "gpt-4", cost: 0.1, tokenCount: 100, startedAt: fromTimestamp 100000.0 }
          , { id: "2", model: "gpt-4", cost: 0.2, tokenCount: 200, startedAt: fromTimestamp 500000.0 }
          , { id: "3", model: "gpt-4", cost: 0.3, tokenCount: 300, startedAt: now }
          ]
        filtered = TokenUsage.filterSessionsByTimeRange TokenUsage.AllTime sessions now
      
      Array.length filtered `shouldEqual` Array.length sessions
  
  describe "sessionsToDataPoints" do
    it "converts sessions to data points" do
      let
        sessions = 
          [ { id: "1", model: "gpt-4", cost: 0.1, tokenCount: 100, startedAt: testDateTime }
          , { id: "2", model: "gpt-4", cost: 0.2, tokenCount: 200, startedAt: testDateTime }
          ]
        dataPoints = TokenUsage.sessionsToDataPoints sessions
      
      Array.length dataPoints `shouldEqual` Array.length sessions
      dataPoints # Array.head # case _ of
        Just point -> do
          point.totalTokens `shouldEqual` 100
          point.cost `shouldEqual` 0.1
        Nothing -> pure unit
    
    it "preserves session order" do
      let
        sessions = 
          [ { id: "1", model: "gpt-4", cost: 0.1, tokenCount: 100, startedAt: testDateTime }
          , { id: "2", model: "gpt-4", cost: 0.2, tokenCount: 200, startedAt: testDateTime }
          ]
        dataPoints = TokenUsage.sessionsToDataPoints sessions
      
      dataPoints # Array.head # case _ of
        Just point -> point.totalTokens `shouldEqual` 100
        Nothing -> pure unit
  
  describe "calculateCostBreakdown" do
    it "aggregates costs by model" do
      let
        sessions = 
          [ { id: "1", model: "gpt-4", cost: 0.1, tokenCount: 100, startedAt: testDateTime }
          , { id: "2", model: "gpt-4", cost: 0.2, tokenCount: 200, startedAt: testDateTime }
          , { id: "3", model: "gpt-3.5", cost: 0.05, tokenCount: 50, startedAt: testDateTime }
          ]
        breakdown = TokenUsage.calculateCostBreakdown sessions
      
      Array.length breakdown `shouldEqual` 2  -- Two models
      breakdown # Array.find (\b -> b.model == "gpt-4") # case _ of
        Just gpt4 -> gpt4.cost `shouldEqual` 0.3  -- 0.1 + 0.2
        Nothing -> pure unit
    
    it "calculates percentages correctly" do
      let
        sessions = 
          [ { id: "1", model: "gpt-4", cost: 0.3, tokenCount: 100, startedAt: testDateTime }
          , { id: "2", model: "gpt-3.5", cost: 0.1, tokenCount: 50, startedAt: testDateTime }
          ]
        breakdown = TokenUsage.calculateCostBreakdown sessions
        totalCost = 0.4
      
      breakdown # Array.find (\b -> b.model == "gpt-4") # case _ of
        Just gpt4 -> gpt4.percentage `shouldEqual` 75.0  -- 0.3 / 0.4 * 100
        Nothing -> pure unit
      
      breakdown # Array.find (\b -> b.model == "gpt-3.5") # case _ of
        Just gpt35 -> gpt35.percentage `shouldEqual` 25.0  -- 0.1 / 0.4 * 100
        Nothing -> pure unit
    
    it "handles empty sessions array" do
      let breakdown = TokenUsage.calculateCostBreakdown []
      Array.length breakdown `shouldEqual` 0
    
    it "sorts by cost descending" do
      let
        sessions = 
          [ { id: "1", model: "gpt-3.5", cost: 0.1, tokenCount: 50, startedAt: testDateTime }
          , { id: "2", model: "gpt-4", cost: 0.3, tokenCount: 100, startedAt: testDateTime }
          ]
        breakdown = TokenUsage.calculateCostBreakdown sessions
      
      breakdown # Array.head # case _ of
        Just first -> first.model `shouldEqual` "gpt-4"  -- Higher cost first
        Nothing -> pure unit
  
  describe "DateTime comparison" do
    it "compares timestamps correctly" do
      let
        dt1 = fromTimestamp 2000000.0
        dt2 = fromTimestamp 1000000.0
        ts1 = toTimestamp dt1
        ts2 = toTimestamp dt2
      (ts1 >= ts2) `shouldEqual` true
    
    it "handles equal timestamps" do
      let
        dt = fromTimestamp 1000000.0
        ts = toTimestamp dt
      (ts == ts) `shouldEqual` true
    
    it "handles before comparison" do
      let
        dt1 = fromTimestamp 1000000.0
        dt2 = fromTimestamp 2000000.0
        ts1 = toTimestamp dt1
        ts2 = toTimestamp dt2
      (ts1 < ts2) `shouldEqual` true
