-- | Unit tests for state reducer
-- | Based on spec 71-UNIT-TESTING.md
module Test.Sidepanel.State.ReducerSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Sidepanel.State.Reducer (reduce, updateBalance, updateSessionFromExisting, createSessionFromUpdate)
import Sidepanel.State.AppState (initialState, AppState)
import Sidepanel.State.Balance (initialBalanceState, BalanceState)
import Sidepanel.State.Actions (Action(..), BalanceUpdate, SessionUpdate)
import Data.DateTime (DateTime)
import Test.Sidepanel.TestFixtures (testDateTime, defaultTestSession, createTestDateTime)

spec :: Spec Unit
spec = describe "State Reducer" do
  describe "reduce" do
    it "handles Connected action" do
      let result = reduce initialState Connected
      result.connected `shouldEqual` true
    
    it "handles Disconnected action" do
      let result = reduce initialState Disconnected
      result.connected `shouldEqual` false
    
    it "toggles connection state correctly" do
      let state1 = reduce initialState Connected
      state1.connected `shouldEqual` true
      let state2 = reduce state1 Disconnected
      state2.connected `shouldEqual` false
      let state3 = reduce state2 Connected
      state3.connected `shouldEqual` true
    
    it "handles BalanceUpdated action" do
      let update = { diem: 42.0, usd: 10.0, effective: 52.0, consumptionRate: 2.3, timeToDepletion: Just 18.0, todayUsed: 7.5 }
      let result = reduce initialState (BalanceUpdated update)
      case result.balance.venice of
        Just venice -> do
          venice.diem `shouldEqual` 42.0
          venice.usd `shouldEqual` 10.0
          venice.effective `shouldEqual` 52.0
        Nothing -> false `shouldEqual` true
    
    it "handles BalanceUpdated with zero values" do
      let update = { diem: 0.0, usd: 0.0, effective: 0.0, consumptionRate: 0.0, timeToDepletion: Nothing, todayUsed: 0.0 }
      let result = reduce initialState (BalanceUpdated update)
      case result.balance.venice of
        Just venice -> do
          venice.diem `shouldEqual` 0.0
          venice.usd `shouldEqual` 0.0
          venice.effective `shouldEqual` 0.0
        Nothing -> false `shouldEqual` true
    
    it "handles BalanceUpdated with very large values" do
      let update = { diem: 1.0e10, usd: 5.0e9, effective: 1.5e10, consumptionRate: 1.0e6, timeToDepletion: Just 1.5e4, todayUsed: 1.0e9 }
      let result = reduce initialState (BalanceUpdated update)
      case result.balance.venice of
        Just venice -> do
          venice.diem `shouldEqual` 1.0e10
          venice.usd `shouldEqual` 5.0e9
        Nothing -> false `shouldEqual` true
    
    it "handles multiple BalanceUpdated actions" do
      let update1 = { diem: 100.0, usd: 50.0, effective: 150.0, consumptionRate: 10.0, timeToDepletion: Just 15.0, todayUsed: 0.0 }
      let state1 = reduce initialState (BalanceUpdated update1)
      let update2 = { diem: 200.0, usd: 100.0, effective: 300.0, consumptionRate: 20.0, timeToDepletion: Just 15.0, todayUsed: 50.0 }
      let state2 = reduce state1 (BalanceUpdated update2)
      case state2.balance.venice of
        Just venice -> do
          venice.diem `shouldEqual` 200.0
          venice.usd `shouldEqual` 100.0
        Nothing -> false `shouldEqual` true
    
    it "handles SessionUpdated action for new session" do
      let update = { id: "sess_123", model: "llama-3.3-70b", promptTokens: 1000, completionTokens: 500, totalTokens: 1500, cost: 0.01, messageCount: 5, startedAt: Nothing }
      let result = reduce initialState (SessionUpdated update)
      case result.session of
        Just session -> do
          session.id `shouldEqual` "sess_123"
          session.model `shouldEqual` "llama-3.3-70b"
          session.promptTokens `shouldEqual` 1000
          session.completionTokens `shouldEqual` 500
          session.totalTokens `shouldEqual` 1500
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
    
    it "handles SessionUpdated with zero tokens" do
      let update = { id: "sess_zero", model: "test", promptTokens: 0, completionTokens: 0, totalTokens: 0, cost: 0.0, messageCount: 1, startedAt: Nothing }
      let result = reduce initialState (SessionUpdated update)
      case result.session of
        Just session -> do
          session.totalTokens `shouldEqual` 0
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
    
    it "handles SessionUpdated with very large token counts" do
      let update = { id: "sess_large", model: "test", promptTokens: 1000000, completionTokens: 2000000, totalTokens: 3000000, cost: 100.0, messageCount: 1000, startedAt: Nothing }
      let result = reduce initialState (SessionUpdated update)
      case result.session of
        Just session -> do
          session.totalTokens `shouldEqual` 3000000
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
    
    it "handles SessionUpdated updating existing session" do
      let update1 = { id: "sess_1", model: "model1", promptTokens: 100, completionTokens: 200, totalTokens: 300, cost: 0.01, messageCount: 2, startedAt: Nothing }
      let state1 = reduce initialState (SessionUpdated update1)
      let update2 = { id: "sess_1", model: "model1", promptTokens: 200, completionTokens: 400, totalTokens: 600, cost: 0.02, messageCount: 4, startedAt: Nothing }
      let state2 = reduce state1 (SessionUpdated update2)
      case state2.session of
        Just session -> do
          session.id `shouldEqual` "sess_1"
          session.totalTokens `shouldEqual` 600
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
    
    it "handles SessionCleared action" do
      let withSession = initialState { session = Just defaultTestSession }
      let result = reduce withSession SessionCleared
      result.session `shouldEqual` Nothing
    
    it "handles SessionCleared when no session exists (idempotent)" do
      let result = reduce initialState SessionCleared
      result.session `shouldEqual` Nothing
    
    it "preserves balance when clearing session" do
      let update = { diem: 100.0, usd: 50.0, effective: 150.0, consumptionRate: 10.0, timeToDepletion: Just 15.0, todayUsed: 0.0 }
      let state1 = reduce initialState (BalanceUpdated update)
      let sessionUpdate = { id: "sess_1", model: "test", promptTokens: 100, completionTokens: 200, totalTokens: 300, cost: 0.01, messageCount: 1, startedAt: Nothing }
      let state2 = reduce state1 (SessionUpdated sessionUpdate)
      let state3 = reduce state2 SessionCleared
      case state3.balance.venice of
        Just venice -> do
          venice.diem `shouldEqual` 100.0
          venice.usd `shouldEqual` 50.0
        Nothing -> false `shouldEqual` true
      state3.session `shouldEqual` Nothing
  
  describe "updateBalance" do
    it "updates Venice balance correctly" do
      let balance = initialBalanceState
      let update = { diem: 50.0, usd: 20.0, effective: 70.0, consumptionRate: 1.5, timeToDepletion: Just 33.0, todayUsed: 10.0 }
      let result = updateBalance balance update
      case result.venice of
        Just venice -> do
          venice.diem `shouldEqual` 50.0
          venice.usd `shouldEqual` 20.0
          venice.effective `shouldEqual` 70.0
          venice.effective `shouldEqual` (venice.diem + venice.usd)
        Nothing -> false `shouldEqual` true
    
    it "updates balance with zero values" do
      let balance = initialBalanceState
      let update = { diem: 0.0, usd: 0.0, effective: 0.0, consumptionRate: 0.0, timeToDepletion: Nothing, todayUsed: 0.0 }
      let result = updateBalance balance update
      case result.venice of
        Just venice -> do
          venice.diem `shouldEqual` 0.0
          venice.usd `shouldEqual` 0.0
          venice.effective `shouldEqual` 0.0
        Nothing -> false `shouldEqual` true
    
    it "updates balance with very large values" do
      let balance = initialBalanceState
      let update = { diem: 1.0e10, usd: 5.0e9, effective: 1.5e10, consumptionRate: 1.0e6, timeToDepletion: Just 1.5e4, todayUsed: 1.0e9 }
      let result = updateBalance balance update
      case result.venice of
        Just venice -> do
          venice.diem `shouldEqual` 1.0e10
          venice.usd `shouldEqual` 5.0e9
          let expected = venice.diem + venice.usd
          let diff = if venice.effective > expected then venice.effective - expected else expected - venice.effective
          diff < 0.01 `shouldBeTrue`
        Nothing -> false `shouldEqual` true
    
    it "preserves effective balance equals diem + usd" do
      let balance = initialBalanceState
      let update1 = { diem: 100.0, usd: 50.0, effective: 150.0, consumptionRate: 10.0, timeToDepletion: Just 15.0, todayUsed: 0.0 }
      let result1 = updateBalance balance update1
      case result1.venice of
        Just venice -> venice.effective `shouldEqual` (venice.diem + venice.usd)
        Nothing -> false `shouldEqual` true
      
      let update2 = { diem: 200.0, usd: 100.0, effective: 300.0, consumptionRate: 20.0, timeToDepletion: Just 15.0, todayUsed: 50.0 }
      let result2 = updateBalance result1 update2
      case result2.venice of
        Just venice -> venice.effective `shouldEqual` (venice.diem + venice.usd)
        Nothing -> false `shouldEqual` true
  
  describe "updateSessionFromExisting" do
    it "preserves startedAt from existing session" do
      let existing = { id: "sess_1", model: "model1", promptTokens: 100, completionTokens: 50, totalTokens: 150, cost: 0.01, messageCount: 2, startedAt: testDateTime }
      let update = { id: "sess_1", model: "model1", promptTokens: 200, completionTokens: 100, totalTokens: 300, cost: 0.02, messageCount: 4, startedAt: Nothing }
      let result = updateSessionFromExisting existing update
      result.startedAt `shouldEqual` existing.startedAt
      result.totalTokens `shouldEqual` 300
      result.totalTokens `shouldEqual` (result.promptTokens + result.completionTokens)
    
    it "updates token counts correctly" do
      let existing = { id: "sess_1", model: "model1", promptTokens: 100, completionTokens: 50, totalTokens: 150, cost: 0.01, messageCount: 2, startedAt: testDateTime }
      let update = { id: "sess_1", model: "model1", promptTokens: 500, completionTokens: 250, totalTokens: 750, cost: 0.05, messageCount: 10, startedAt: Nothing }
      let result = updateSessionFromExisting existing update
      result.promptTokens `shouldEqual` 500
      result.completionTokens `shouldEqual` 250
      result.totalTokens `shouldEqual` 750
      result.totalTokens `shouldEqual` (result.promptTokens + result.completionTokens)
    
    it "updates cost correctly" do
      let existing = { id: "sess_1", model: "model1", promptTokens: 100, completionTokens: 50, totalTokens: 150, cost: 0.01, messageCount: 2, startedAt: testDateTime }
      let update = { id: "sess_1", model: "model1", promptTokens: 200, completionTokens: 100, totalTokens: 300, cost: 0.10, messageCount: 4, startedAt: Nothing }
      let result = updateSessionFromExisting existing update
      result.cost `shouldEqual` 0.10
      result.cost >= 0.0 `shouldBeTrue`
    
    it "preserves session ID" do
      let existing = { id: "sess_1", model: "model1", promptTokens: 100, completionTokens: 50, totalTokens: 150, cost: 0.01, messageCount: 2, startedAt: testDateTime }
      let update = { id: "sess_1", model: "model2", promptTokens: 200, completionTokens: 100, totalTokens: 300, cost: 0.02, messageCount: 4, startedAt: Nothing }
      let result = updateSessionFromExisting existing update
      result.id `shouldEqual` "sess_1"
  
  describe "createSessionFromUpdate" do
    it "creates session from update with new startedAt" do
      let update = { id: "sess_new", model: "model1", promptTokens: 100, completionTokens: 50, totalTokens: 150, cost: 0.01, messageCount: 1, startedAt: Nothing }
      let result = createSessionFromUpdate update
      result.id `shouldEqual` "sess_new"
      result.totalTokens `shouldEqual` 150
      result.totalTokens `shouldEqual` (result.promptTokens + result.completionTokens)
    
    it "creates session with zero tokens" do
      let update = { id: "sess_zero", model: "model1", promptTokens: 0, completionTokens: 0, totalTokens: 0, cost: 0.0, messageCount: 1, startedAt: Nothing }
      let result = createSessionFromUpdate update
      result.totalTokens `shouldEqual` 0
      result.totalTokens `shouldEqual` (result.promptTokens + result.completionTokens)
    
    it "creates session with very large token counts" do
      let update = { id: "sess_large", model: "model1", promptTokens: 1000000, completionTokens: 2000000, totalTokens: 3000000, cost: 100.0, messageCount: 1000, startedAt: Nothing }
      let result = createSessionFromUpdate update
      result.totalTokens `shouldEqual` 3000000
      result.totalTokens `shouldEqual` (result.promptTokens + result.completionTokens)